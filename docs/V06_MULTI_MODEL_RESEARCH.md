# Rapport de Recherche Multi-Modèles : Pistes d'Amélioration & Directions d'Auto-Research pour `lean-native` (v0.6+)

- **Dépôt audité** : `https://github.com/Th0rgal/lean-native` (commit `29425b6`, v0.5.0)
- **Panel de 5 sous-agents de recherche déployés en parallèle (mode lecture seule `writer: false`)** :
  1. **Claude Fable 5.1** (`anthropic/claude-fable-5-1`, `effort=high`) — Mission `df3a379c-2218-4059-9691-0f53718377f8` (`18 631` caractères)
  2. **Claude Opus 5.5** (`anthropic/claude-opus-5-5`, `effort=high`) — Missions `8fe58821-b1ca-49cc-be7a-954b8ade4e4f` & `20693832-cb6a-49bc-b1e0-a08a40822da6` (`14 127` caractères + 51 étapes de sondes adversariales)
  3. **Gemini 4 Argon** (`google/gemini-4-argon`, `effort=high`) — Mission `d626f6ae-af42-4853-99ba-e222f315c4a1` (`24 206` caractères)
  4. **GPT-6 Astra** (`openai/gpt-6-astra`, `effort=high`) — Mission `bd1f42d0-d533-4b6f-8809-58133b4f7cdd` (`35 924` caractères)
  5. **GPT-6.1 Sol High** (`openai/gpt-6.1-sol`, `effort=high`) — Mission `126a0093-829d-4936-b6b3-fbc1b24693b1` (`29 496` caractères)

---

## 1. Synthèse Comparative & Convergence des 5 Modèles

| Dimension d'Audit | Claude Fable 5.1 | Claude Opus 5.5 | Gemini 4 Argon | GPT-6 Astra | GPT-6.1 Sol High |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **1. Liaison Passe ↔ Preuve (`L3`)** | Ajouter un champ dépendant `sound : ∀ d, CodeRefines d.body (run d).body` dans `TransformPass` et supprimer le registre de chaînes `verifiedTheoremRegistry`. | Prouver le validateur `verifyOptPluginGate_sound` ou faire émettre aux plugins une **trace de réécritures** vérifiée dans le noyau. | Prouver `borrow_rc_elision_sound` (car `LoopVectorizeOpt` cite aujourd'hui `hoistExclusivity_sound`) et le lemme pont `validateTranslationDecl_sound`. | Exiger que `CertChecker` vérifie que le théorème s'applique aux AST `(src, tgt)` réels au lieu de vérifier l'appartenance d'une chaîne à une liste. | A prouvé expérimentalement qu'un certificat factice (`changed=true`, `theoremRef=CodeRefines.refl`) passe `verifySingleCert`. |
| **2. Sémantique `Eval.lean` & `Refinement.lean`** | Modéliser un tas à compteurs `rc : Nat` (Ullrich & de Moura, *Counting Immutable Beans*), donner une dénotation à `parFor`, et aligner `x / 0 = 0` sur Lean 4. | Séparer `OutOfFuel` et `revert(code)` (Panic EVM `0x11`/`0x12`) de `UBError` ; retirer les cas ad-hoc `tuple + 0 = tuple` dans `evalBinOp`. | Remplacer `exclusive : Bool` par `refCount : Nat` dans `ArrayBuffer` ; évaluer réellement `parFor` pour prouver `seqFor_to_parFor_refines`. | Séparer `OutOfFuel` du retour `.ok (.unit, st)` à `fuel = 0` ; autoriser une simulation à pas découplés (et non au même `fuel` exact). | A démontré à `fuel = 2` qu'une optimisation SROA valide viole `CodeRefines` car `fuel = 0` retourne `.ok (.unit, st)`. |
| **3. Bugs Concrets & Divergences Backend Découverts** | `x / 0` et `x % 0` : Lean retourne `0` et `x`, `Eval` retourne `UBError`, et `LLVM.lean` divise par `1` (`select isZero, 1, rhs`). | `sar` sur `u64` (`Eval` étend en `UInt256` sans signe avant de décaler, `LLVM` émet `ashr i64`) ; `SymbolicTV` confond `mulDivDown` et `(a*b)/d` sur petits échantillons `1..8`. | `Metal.lean` : `ln_u256_mul_lo` omet les retenues hautes `ln_mul64_hi` à l'étage `2 -> 3` ; `dot_product_u64` Metal tronque à `atomic_uint` 32 bits ; `SymbolicTV` tronque `constU256` à `lo0`. | `LLVM.lean` : `.not` en `i64` émet `xor i64 x, 1` au lieu de `xor -1` ; `shl/shr u256` masque avec `255` au lieu de renvoyer `0` si `>= 256` ; `addChecked256` ignore le flag d'overflow `i1`. | A exécuté le code généré et confirmé : `not(0) = 1` en LLVM contre `2^64-1` dans `Eval` ; `sar(2^63, 1)` diverge ; `ln_u256_mul_lo(max256, max256)` retourne `[1,0,0,4]` au lieu de `[1,0,0,0]`. |
| **4. Unification IR & Réduction TCB** | IR typée sur `BitVec w` + un seul interpréteur générique `eval [ValueDomain D]` partagé entre concret et symbolique + preuve de round-trip `Codec`. | Unifier `Eval` et `SymExpr` sur `BitVec w`, retirer `SymbolicTV` ad-hoc au profit d'un vérificateur de traces d'e-graph, et lancer `alive-tv` en CI. | Fusionner `ScalarExpr`/`LNIRExpr` en `Expr (t : LNIRType)` (`Val .i64 = UInt64`, zéro `UBError.typeError`) + `LowGPUIR` impératif unique pour PTX/MLIR/Metal. | Vérificateur de bonne formation (`WellFormed`) prouvé + durcissement de `Bridge.lean` (arrêter le matching par suffixe de nom et le `--allow-multiple-definition`). | Séparer 3 dialectes explicites (cœur scalaire typé, IR mémoire/ownership, IR parallèle) et garantir un propriétaire unique par symbole dans `build-exe`. |
| **5. Performance CPU / GPU / EVM** | `mulDiv` 512/256 par algorithme de Knuth D / Remco Bloemen sur limbs 64 bits (**10–50x** vs `udiv i512`), mémoire unifiée zero-copy NVLink-C2C sur GB10, 4 accumulateurs ILP. | Modèle de coût calibré (`llvm-mca` / matériel), `mulx`/`adcx`/`adox` (x86) et `umulh`/`adcs` (ARM64) pour `u256`, limbs 32 bits (`IMAD`) sur GPU. | ARM64 `"target-cpu"="neoverse-v2"` + `+sve2`, registres SSA `phi` dans `seqFor` (élimine la régression holdout de 11%), PTX `shfl.sync.down.b32` + padding `+1` sur `tileB`, Robin Hood hashing EVM. | Multiversioning SIMD (`NEON`/`SVE2`, `AVX2`/`AVX-512DQ`), réduction PTX par warp (`shfl.sync` sur paires 32 bits), élimination des annotations `noalias`/`nsw` non prouvées. | Compiler et chronométrer les **vrais artefacts émis** par `lean-native` dans `run_benchmarks.py` au lieu des fichiers C/CUDA manuscrits de référence. |
| **6. Auto-Research & Superoptimisation** | **E-Graphs à explications (Flatt et al.)** hors TCB + vérificateur par réflexion (`normSymExpr_sound`) en L3 + harvesting Souper contre `opt -O3` + vrai benchmark A/B par worktree. | **Mutation testing** de la porte de vérification (taux de faux positifs = 0), `egg`/`egglog` avec traces de règles prouvées, synthèse d'ordonnancement GPU façon Halide/GPUVerify. | `LeanNative/Transform/EGraph.lean` avec reconstruction de preuve par congruence + boucle **CEGIS** couplée à `lean-native-core worker` (`0.07 ms`) et au démon Zygote de `turbo-lean`. | Fermer tous les fallbacks permissifs (`check_shard_with_fallback`, `tested = num_states`, temps codés en dur), appliquer un vrai patch git dans le worktree et vérifier le terme de preuve dans le noyau. | A démontré que `theorem audit_false : False := by exact True.intro` passe le fallback lexical de `turbo_lean_bridge.py` ; exige une vérification noyau stricte et un contrôle statistique rigoureux. |

---

## 2. Les 10 Failles & Bugs Concrets Découverts par l'Audit Multi-Modèles

L'audit croisé des 5 modèles (combiné aux sondes exécutées par **Opus 5.5**, **GPT-6 Astra** et **GPT-6.1 Sol High**) a mis au jour **10 bugs et écarts sémantiques précis** dans la v0.5 :

1. **Bug d'abaissement `UnaryOp.not` en LLVM (`LeanNative/Backend/LLVM.lean:518-524`)** *(trouvé et exécuté par GPT-6.1 Sol High & GPT-6 Astra)* :
   - `Eval.lean` évalue `.not (.u64 0)` en `~~~0 = 18446744073709551615` (`0xffffffffffffffff`, complément bit-à-bit), tandis que `LLVM.lean` émet `xor i64 %aVal, 1`, ce qui retourne `1` !
2. **Bug d'abaissement `BinOp.sar` sur `UInt64` (`LeanNative/Semantics/Eval.lean:90-95` vs `LeanNative/Backend/LLVM.lean:494-497`)** *(trouvé par Opus 5.5, GPT-6 Astra & GPT-6.1 Sol High)* :
   - Dans `Eval.lean`, `.sar (.u64 a) (.u64 b)` convertit `a` en `UInt256` non signé (`ofUInt64 a`, donc bit de signe 255 = `0`) avant d'appeler `UInt256.sar` ! Pour `a = 0x8000000000000000` et `b = 1`, `Eval.lean` retourne `0x4000000000000000` (décalage logique) alors que `LLVM.lean` (`ashr i64`) retourne `0xc000000000000000` (décalage arithmétique signé 64 bits).
3. **Bug de retenue haute dans la multiplication 256-bit Metal (`LeanNative/Backend/Metal.lean:97-112`)** *(trouvé par Gemini 4 Argon, GPT-6 Astra & GPT-6.1 Sol High)* :
   - Dans `ln_u256_mul_lo`, le calcul du limb 3 (`m3`) omet les parties hautes 64 bits des produits croisés de rang 2 (`ln_mul64_hi(a.l0, b.l2)`, `ln_mul64_hi(a.l1, b.l1)`, `ln_mul64_hi(a.l2, b.l0)`). Pour `max256 * max256`, la fonction retourne les limbs `[1, 0, 0, 4]` au lieu de `[1, 0, 0, 0]`.
4. **Troncature 32 bits dans la réduction `dot_product_u64` Metal (`LeanNative/Backend/Metal.lean:152-168`)** *(trouvé par Gemini 4 Argon, GPT-6 Astra & GPT-6.1 Sol High)* :
   - L'accumulation inter-groupes utilise `device atomic_uint* out_lo` et tronque le résultat 64 bits via `(uint)(sdata[0] & 0xffffffffUL)`.
5. **Troncature de `constU256` et confusion `mulDivDown`/`mulDivUp` dans `SymbolicTV.lean` (`LeanNative/Proofs/SymbolicTV.lean:318-329`)** *(trouvé par Opus 5.5, Gemini 4 Argon & GPT-6 Astra)* :
   - `symEvalExpr` projette `.constU256 val` sur son seul limb bas `.constU64 val.lo0` (ignorant les 192 bits hauts) et représente `mulDivDown` et `mulDivUp` par la même expression 64 bits `.binOp .div (.binOp .mul sa.expr sb.expr) sd.expr`. De plus, l'échantillonneur concret tire des valeurs entre `1` et `8` (`(r % 8) + 1`), ce qui ne déclenche jamais d'overflow 256 bits.
6. **Ignorance du bit d'overflow `i1` sur `addChecked256`/`subChecked256`/`mulChecked256` et `mulDiv` dans `LLVM.lean` (`LeanNative/Backend/LLVM.lean:389-403, 582-617`)** *(trouvé par Opus 5.5, Gemini 4 Argon, GPT-6 Astra & GPT-6.1 Sol High)* :
   - `LLVM.lean` appelle `@llvm.uadd.with.overflow.i256` mais extrait uniquement la valeur (`extractvalue { i256, i1 } %ov, 0`) sans brancher vers `@llvm.trap()` lorsque le bit d'overflow vaut `1`, et `mulDivDown`/`Up` tronque `quot512` en `i256` sans vérifier `quot512 >= 2^256`.
7. **Sémantique du `fuel = 0` retournant `.ok (.unit, st)` (`LeanNative/Semantics/Eval.lean:383-384`)** *(trouvé par Opus 5.5, GPT-6 Astra & GPT-6.1 Sol High)* :
   - Lorsque le `fuel` atteint `0`, `evalCode` retourne `.ok (.unit, st)` au lieu d'une erreur dédiée `OutOfFuel`. Comme `CodeRefines` quantifie au même `fuel` pour `src` et `tgt`, toute passe qui réduit ou augmente le nombre de `letBind` diverge exactement au `fuel` frontière.
8. **Aveuglement de `evalCode` sur `incRef`, `decRef`, `parFor` et `call` (`LeanNative/Semantics/Eval.lean:363-366, 405-434`)** *(unanime sur les 5 modèles)* :
   - `parFor` lie `outVar` à `.sarrayId 0` sans exécuter le noyau parallèle, ce qui permet à `validateTranslationDecl` d'accepter le remplacement de `mapScaleAdd 1 0` par `mapScaleAdd 2 99`.
9. **Régression CPU de 7–12 % sur `holdout_bitwise` / `holdout_loop_bounds` (`LeanNative/Backend/LLVM.lean:485-497, 1146-1160, 1348`)** *(diagnostiqué par Gemini 4 Argon & Fable 5.1)* :
   - Causée par (a) `"target-cpu"="generic"` sur ARM64 au lieu de `"neoverse-v2"`/`"cortex-x925"`, (b) l'utilisation de slots `alloca` par variable au lieu de registres SSA `phi` dans `seqFor`, et (c) l'émission systématique de `and i64 %rVal, 63` même sur des constantes de décalage connues.
10. **Fallbacks permissifs dans `scripts/turbo_lean_bridge.py` et `autoresearch/`** *(trouvé par Fable 5.1, Opus 5.5, GPT-6 Astra & GPT-6.1 Sol High)* :
    - `check_shard_with_fallback` faisait un contrôle lexical en l'absence du démon Zygote, `fast_check_rewrite` plafonnait la boucle Python à `1024` itérations avant d'affecter `tested = num_states`, et `loop.py` évaluait une liste fixe d'hypothèses sans appliquer de patch git réel dans le worktree.

---

## 3. Plan d'Architecture & Directions d'Auto-Research pour `lean-native` v0.6+

### Axe 1 — Fiabilité & Preuves Formelles (Fermeture de la Chaîne de Confiance)
1. **Preuves dans le type (`TransformPass.sound`) et élimination du registre de chaînes** *(Fable 5.1, Astra, Sol)* :
   - Redéfinir `TransformPass` dans [`LeanNative/Transform/Pass.lean`](file:///var/lib/spark-admin/jobs/3730b838-a03b-49e3-bbd2-eb51c132a4e7/lean-native/LeanNative/Transform/Pass.lean) pour qu'une passe de niveau `verifiedKernelProof` transporte directement un théorème `sound : ∀ d, CodeRefines d.body (runDecl d).body` (ou émette un certificat de réécriture inductif `RewriteTrace` rejoué par un vérificateur prouvé `checkTrace_sound`).
2. **Séparation `OutOfFuel` / `Revert` / `UBError` et simulation découplée du `fuel`** *(Opus 5.5, Astra, Sol)* :
   - Remplacer le type de retour de `evalCode` par un résultat distinguant :
     - `.ok (v, st)` (terminaison normale),
     - `.revert code` (erreur arithmétique vérifiée / division par zéro EVM Panic `0x11` / `0x12`, qui **doit être préservée** par toute optimisation !),
     - `.outOfFuel` (budget d'évaluation épuisé, ignoré dans la précondition de `CodeRefines`),
     - `.ub err` (véritable erreur de typage ou d'accès hors bornes).
   - Définir `CodeRefines src tgt` par : `∀ f_src env st res, evalCode f_src env st src = res → res ≠ .outOfFuel → ∃ f_tgt, evalCode f_tgt env st tgt = res`.
3. **Modèle mémoire affine à comptage de références (`refCount : Nat`) et dénotation de `parFor`** *(Fable 5.1, Gemini 4 Argon)* :
   - Remplacer `exclusive : Bool` par `refCount : Nat` dans `HeapState.ArrayBuffer`, donner leur vraie sémantique à `incRef`, `decRef` et `sarrayEnsureExclusive` (clonage de buffer si `refCount > 1`), et prouver le théorème `borrow_rc_elision_sound` (*Counting Immutable Beans*).
   - Évaluer fonctionnellement `parFor` sur les éléments du buffer dans `Eval.lean` et prouver `seqFor_to_parFor_refines`.
4. **Validateur Symbolique par Réflexion (`normSymExpr_sound`)** *(Fable 5.1, Opus 5.5, Gemini 4 Argon)* :
   - Étendre `SymExpr` aux constantes 256 bits complètes (`UInt256`), rendre le rang commutatif strictement injectif, et prouver dans le noyau Lean `theorem normSymExpr_sound : ∀ env, evalSym env (normSymExpr s) = evalSym env s`. Cela ferme l'hypothèse `h_gate_sound` de `LeanNative.Spec.untrusted_opt_plugin_code_refines` (Law 1) sur le fragment sans boucles !

### Axe 2 — Simplicité, Unification des IR & Réduction de la TCB
1. **Famille inductive intrinsèquement typée (`Expr (t : LNIRType)`) et `ValueDomain D` générique** *(Fable 5.1, Opus 5.5, Gemini 4 Argon)* :
   - Unifier `UInt64` et `UInt256` sur `BitVec w` (`w ∈ {1, 8, 16, 32, 64, 256}`).
   - Remplacer les trois évaluateurs parallèles (`Eval.lean`, `SymbolicTV.lean`, `Superopt.lean`) par un unique interpréteur générique `evalGeneric [ValueDomain D]` instancié une fois sur le domaine concret et une fois sur le domaine symbolique.
2. **Vrai AST bas niveau `LowGPUIR` et suppression des templates GPU nommés** *(Gemini 4 Argon, Fable 5.1, Astra, Sol)* :
   - Remplacer les branchements par nom (`d.name == "dot_product_u64"`) dans `GPUIR.lean`, `MLIRGPU.lean` et `Metal.lean` par trois combinateurs algébriques (`map`, `reduce`, `stencil` / `tile2D`) abaissés vers un AST impératif `LowGPUIR` commun (avec pretty-printers PTX 8.0, MLIR et Metal MSL 3.0 de `< 150` lignes chacun).
3. **Durcissement de `Bridge.lean` et isolation des symboles dans `build-exe`** *(Astra, Sol)* :
   - Remplacer la détection par suffixe de chaîne (`tryLowerIntrinsicCall`) par une table de noms complets qualifiés (`Lean.Name`), refuser explicitement toute construction LCNF hors du fragment certifié au lieu de l'approximer, et supprimer `--allow-multiple-definition` lors de l'édition de liens.

### Axe 3 — Performance Matérielle CPU / GPU / EVM 256-Bit
1. **Correction immédiate des 4 bugs de codegen LLVM & Metal** :
   - `LLVM.lean` : `.not` en `i64` → `xor i64 %aVal, -1` ; `.sar` dans `Eval.lean` → décalage signé 64 bits cohérent avec `ashr i64` ; émission du branchement `@llvm.trap()` sur le bit d'overflow `i1` de `addChecked256`/`subChecked256`/`mulChecked256` et sur `quot512 >= 2^256` dans `mulDivDown`/`Up` ; masque de décalage `u256 >= 256 -> 0`.
   - `Metal.lean` : propagation complète des retenues hautes `ln_mul64_hi` de l'étage 2 vers l'étage 3 dans `ln_u256_mul_lo`, et réduction 64 bits complète sans troncature 32 bits dans `dot_product_u64`.
2. **Élimination des `alloca` en boucle et cible ARMv9/SVE2 sur `spark-de79`** *(Gemini 4 Argon, Fable 5.1)* :
   - Émettre `"target-cpu"="neoverse-v2"` (`+sve2,+lse`) sur ARM64, abaisser les variables `letBind` directement en registres SSA LLVM (avec nœuds `phi` pour `idxVar`/`accVar` dans `seqFor`), et supprimer le masque `and i64 ..., 63` lorsque le décalage est une constante `< 64`.
3. **Division 512/256 bits par algorithme de Knuth D / Remco Bloemen sur limbs 64 bits** *(Fable 5.1, Opus 5.5, Astra, Sol)* :
   - Remplacer `udiv i512` (qui génère une division bit-sérielle lente dans LLVM) par une division 512/256 structurée en 4 limbs de 64 bits utilisant `mulx`/`adcx`/`adox` (x86-64) et `umulh`/`adcs` (ARM64), avec fast-path `divq` lorsque la partie haute est nulle (**gain attendu : 10x à 50x** sur les contrats EVM/Verity).
4. **Réductions intra-warp PTX `shfl.sync.down.b32`, `cp.async`, et mémoire unifiée zero-copy sur GB10** *(Gemini 4 Argon, Fable 5.1, Astra)* :
   - Remplacer les 5 derniers niveaux de `bar.sync 0` en shared memory dans `emitPTXDotReduceKernel` par des shuffles registres intra-warp `shfl.sync.down.b32` (sur les deux moitiés 32 bits du `u64`), ajouter un padding d'une colonne (`16 × 17`) sur `tileB_raw` dans `matmul_tiled_u64` pour supprimer les conflits de banques, et utiliser l'allocation cohérente NVLink-C2C / host-pinned sur Grace-Blackwell GB10 pour éliminer le coût de `cudaMemcpyAsync`.

### Axe 4 — Auto-Research de Seconde Génération (E-Graphs Certifiés, CEGIS & Benchmarks A/B Réels)
1. **Moteur d'Equality Saturation à Explications (`LeanNative/Transform/EGraph.lean`)** *(Fable 5.1, Opus 5.5, Gemini 4 Argon, Astra, Sol)* :
   - Implémenter un e-graph compact hors TCB qui sature les expressions scalaires et produit une **explication (trace de réécritures élémentaires)** à la *egg* (Flatt et al.).
   - Le vérificateur du noyau rejoue uniquement cette trace finie étape par étape en appliquant les lemmes de `PeepholeProofs.lean` et `Refinement.trans`, conférant le niveau **`L3 VerifiedKernelProof`** à toute découverte de l'e-graph sans faire confiance à l'algorithme de recherche.
2. **Boucle CEGIS ouverte couplée au démon Zygote de `turbo-lean` et à Souper/LLVM** *(Fable 5.1, Opus 5.5, Gemini 4 Argon)* :
   - Extraire automatiquement les sous-graphes chauds des programmes Lean/Verity compilés, comparer leur abaissement à `opt -O3` pour récolter les optimisations manquées (*harvesting*), filtrer les candidats par empreintes SplitMix64 + boundary 64/256 bits complètes (`0, 1, 2^63, 2^64-1, 2^255, 2^256-1`), et synthétiser automatiquement le théorème Lean 4 vérifié par le noyau via `turbo-lean` avant toute acceptation.
3. **Protocole expérimental A/B strict dans `autoresearch/evaluator.py` et `benchmarks/run_benchmarks.py`** *(unanime sur les 5 modèles)* :
   - Supprimer tous les tableaux de temps de secours (`fallback`) et les vérifications lexicales de shards.
   - Chaque expérience d'`autoresearch` doit appliquer un vrai patch git dans un worktree isolé, compiler les binaires avant/après par `lean-native`, exécuter les binaires réellement émis (avec entrées opaques et consommation du résultat), et appliquer un test statistique corrigé pour les comparaisons multiples (Bonferroni / Holm-Bonferroni) incluant les benchmarks holdout.

---

## 4. Annexes : Extraits Clés par Modèle

Les 5 rapports intégraux ont été archivés au cours de la session :
- **Claude Fable 5.1** : `18 631` caractères (focus : `TransformPass.sound`, validateur par réflexion Tristan & Leroy, e-graphs à explications, `mulDiv` Knuth D, mémoire unifiée GB10).
- **Claude Opus 5.5** : `14 127` caractères (focus : sondes adversariales sur `SymbolicTV` et `mulDivDown`, distinction `OutOfFuel` vs `revert(code)` EVM Panic `0x11`/`0x12`, mutation testing de la porte de vérification).
- **Gemini 4 Argon** : `24 206` caractères (focus : `Expr (t : LNIRType)` indexé, `ValueDomain D`, `refCount : Nat` & `borrow_rc_elision_sound`, `LowGPUIR`, `shfl.sync.down.b32`, padding shared memory `+1`, ARM64 `neoverse-v2` + SSA `phi`).
- **GPT-6 Astra** : `35 924` caractères (focus : audit formel ligne à ligne des 5 lois de `Spec.lean`, `Bridge.lean`, `--allow-multiple-definition`, multiversioning SIMD, fermeture de la chaîne expérimentale `autoresearch`).
- **GPT-6.1 Sol High** : `29 496` caractères (focus : preuves négatives exécutées sur `not(0)`, `sar(2^63, 1)`, `ln_u256_mul_lo(max256, max256)`, `fuel = 2` sur SROA, et test adversarial du fallback lexical `turbo_lean_bridge.py`).
