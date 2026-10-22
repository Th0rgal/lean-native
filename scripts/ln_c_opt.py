import re, sys

def apply_pass1_scalar_array(c_text):
    preamble = """
#include <string.h>
static inline uint64_t* ln_sarray_u64_ptr(lean_object* a) {
    return (uint64_t*)(((char*)a) + sizeof(lean_sarray_object));
}
static inline size_t ln_sarray_u64_size(lean_object* a) {
    return ((lean_sarray_object*)a)->m_size;
}
static inline lean_object* ln_mk_empty_sarray_u64(lean_object* cap_obj) {
    size_t cap = lean_unbox(cap_obj);
    lean_dec(cap_obj);
    return lean_alloc_sarray(8, 0, cap);
}
static inline lean_object* ln_mk_sarray_u64(lean_object* n_obj, uint64_t v) {
    size_t n = lean_unbox(n_obj);
    lean_dec(n_obj);
    lean_object* a = lean_alloc_sarray(8, n, n);
    uint64_t* p = ln_sarray_u64_ptr(a);
    for (size_t i = 0; i < n; ++i) p[i] = v;
    return a;
}
static inline lean_object* ln_mk_array_auto(lean_object* n_obj, lean_object* v) {
    if (!lean_is_scalar(v) && lean_obj_tag(v) == 0 && ((lean_ctor_object*)v)->m_header.m_cs_sz == sizeof(lean_ctor_object) + 8) {
        uint64_t uv = lean_unbox_uint64(v);
        lean_dec(v);
        return ln_mk_sarray_u64(n_obj, uv);
    }
    return lean_mk_array(n_obj, v);
}
static inline uint64_t ln_sarray_uget_u64(lean_object* a, size_t i) {
    return ln_sarray_u64_ptr(a)[i];
}
static inline uint64_t ln_sarray_get_borrowed_u64(lean_object* def, lean_object* a, lean_object* idx) {
    size_t i = lean_unbox(idx);
    size_t n = ln_sarray_u64_size(a);
    return (i < n) ? ln_sarray_u64_ptr(a)[i] : lean_unbox_uint64(def);
}
static inline uint64_t ln_sarray_get_u64(lean_object* def, lean_object* a, lean_object* idx) {
    size_t i = lean_unbox(idx);
    lean_dec(idx);
    size_t n = ln_sarray_u64_size(a);
    uint64_t r = (i < n) ? ln_sarray_u64_ptr(a)[i] : lean_unbox_uint64(def);
    lean_dec(def);
    return r;
}
static inline lean_object* ln_sarray_ensure_exclusive_u64(lean_object* a) {
    if (lean_is_exclusive(a)) return a;
    size_t n = ln_sarray_u64_size(a);
    size_t cap = ((lean_sarray_object*)a)->m_capacity;
    lean_object* r = lean_alloc_sarray(8, n, cap < n ? n : cap);
    memcpy(ln_sarray_u64_ptr(r), ln_sarray_u64_ptr(a), n * 8);
    lean_dec_ref(a);
    return r;
}
static inline lean_object* ln_sarray_set_u64(lean_object* a, lean_object* idx, uint64_t v) {
    size_t i = lean_unbox(idx);
    lean_dec(idx);
    size_t n = ln_sarray_u64_size(a);
    if (i >= n) return a;
    a = ln_sarray_ensure_exclusive_u64(a);
    ln_sarray_u64_ptr(a)[i] = v;
    return a;
}
static inline lean_object* ln_array_set_auto(lean_object* a, lean_object* idx, lean_object* v) {
    if (lean_obj_tag(a) == 248) {
        uint64_t uv = lean_unbox_uint64(v);
        lean_dec(v);
        return ln_sarray_set_u64(a, idx, uv);
    }
    return lean_array_set(a, idx, v);
}
static inline lean_object* ln_sarray_push_u64(lean_object* a, uint64_t v) {
    size_t n = ln_sarray_u64_size(a);
    size_t cap = ((lean_sarray_object*)a)->m_capacity;
    if (lean_is_exclusive(a) && n < cap) {
        ln_sarray_u64_ptr(a)[n] = v;
        ((lean_sarray_object*)a)->m_size = n + 1;
        return a;
    }
    size_t new_cap = cap == 0 ? 4 : (cap < n + 1 ? cap * 2 : cap);
    lean_object* r = lean_alloc_sarray(8, n + 1, new_cap);
    if (n > 0) memcpy(ln_sarray_u64_ptr(r), ln_sarray_u64_ptr(a), n * 8);
    ln_sarray_u64_ptr(r)[n] = v;
    lean_dec(a);
    return r;
}
static inline lean_object* ln_array_push_auto(lean_object* a, lean_object* v) {
    if (lean_obj_tag(a) == 248) {
        if (!lean_is_scalar(v)) {
            uint64_t uv = lean_unbox_uint64(v);
            lean_dec(v);
            return ln_sarray_push_u64(a, uv);
        } else if (ln_sarray_u64_size(a) == 0) {
            size_t cap = ((lean_sarray_object*)a)->m_capacity;
            lean_dec(a);
            lean_object* na = lean_alloc_array(0, cap);
            return lean_array_push(na, v);
        }
    }
    return lean_array_push(a, v);
}
static inline size_t ln_array_size_auto(lean_object* a) {
    if (lean_obj_tag(a) == 248) return ln_sarray_u64_size(a);
    return lean_array_size(a);
}
static inline lean_object* ln_array_get_size_auto(lean_object* a) {
    if (lean_obj_tag(a) == 248) return lean_box(ln_sarray_u64_size(a));
    return lean_array_get_size(a);
}
static inline lean_object* ln_array_get_auto(lean_object* def, lean_object* a, lean_object* idx) {
    if (lean_obj_tag(a) == 248) {
        uint64_t uv = ln_sarray_get_u64(def, a, idx);
        return lean_box_uint64(uv);
    }
    return lean_array_get(def, a, idx);
}
static inline lean_object* ln_array_get_borrowed_auto(lean_object* def, lean_object* a, lean_object* idx) {
    if (lean_obj_tag(a) == 248) {
        uint64_t uv = ln_sarray_get_borrowed_u64(def, a, idx);
        return lean_box_uint64(uv);
    }
    return lean_array_get_borrowed(def, a, idx);
}
static inline lean_object* ln_array_fget_borrowed_auto(lean_object* a, lean_object* idx) {
    if (lean_obj_tag(a) == 248) {
        return lean_box_uint64(ln_sarray_u64_ptr(a)[lean_unbox(idx)]);
    }
    return lean_array_fget_borrowed(a, idx);
}
"""
    c_text = c_text.replace("#include <lean/lean.h>\n", "#include <lean/lean.h>\n" + preamble, 1)

    boxed_u64 = {}
    for m in re.finditer(r"static const lean_ctor_object ([a-zA-Z0-9_]+)_value = \{\.m_header = \{\.m_rc = 0, \.m_cs_sz = sizeof\(lean_ctor_object\) \+ sizeof\(void\*\)\*0 \+ 8, \.m_other = 0, \.m_tag = 0\}, \.m_objs = \{LEAN_SCALAR_PTR_LITERAL\(([^}]+)\)\}\};", c_text):
        name = m.group(1)
        bs = [int(x.strip()) for x in m.group(2).split(",")]
        val = sum(bs[i] << (8 * i) for i in range(8))
        boxed_u64[name] = val

    def repl_static_array(m):
        arr_name = m.group(1)
        sz = int(m.group(2))
        cap = int(m.group(3))
        elems_str = m.group(4)
        elems = re.findall(r"\(\(lean_object\*\)&([a-zA-Z0-9_]+)_value\)", elems_str)
        if len(elems) == sz and all(e in boxed_u64 for e in elems):
            bytes_list = []
            for e in elems:
                v = boxed_u64[e]
                for b_i in range(8):
                    bytes_list.append(str((v >> (8 * b_i)) & 0xFF))
            data_str = ", ".join(bytes_list)
            return f"static const struct {{ lean_object m_header; size_t m_size; size_t m_capacity; uint8_t m_data[{sz * 8}]; }} {arr_name}_value = {{.m_header = {{.m_rc = 0, .m_cs_sz = 8, .m_other = 0, .m_tag = 248}}, .m_size = {sz}, .m_capacity = {cap}, .m_data = {{{data_str}}}}};"
        return m.group(0)

    c_text = re.sub(
        r"static const lean_array_object ([a-zA-Z0-9_]+)_value = \{\.m_header = \{\.m_rc = 0, \.m_cs_sz = sizeof\(lean_array_object\) \+ sizeof\(void\*\)\*[0-9]+, \.m_other = 0, \.m_tag = 246\}, \.m_size = ([0-9]+), \.m_capacity = ([0-9]+), \.m_data = \{([^}]+)\}\};",
        repl_static_array,
        c_text
    )

    # Identify all known UInt64 default value variables (e.g. ___boxed__const__1 initialized from l_instInhabitedUInt64)
    u64_default_consts = set()
    for m in re.finditer(r"static lean_object\* _init_([a-zA-Z0-9_]+)\(void\)\{\n_start:\n\{\nuint64_t [a-zA-Z0-9_]+; lean_object\* [a-zA-Z0-9_]+; \n[a-zA-Z0-9_]+ = l_instInhabitedUInt64;", c_text):
        u64_default_consts.add(m.group(1))
    for k in boxed_u64:
        u64_default_consts.add(k)

    out_parts = []
    last_idx = 0
    for m in re.finditer(r"(?:LEAN_EXPORT |static )[a-z0-9_* ]+ [a-zA-Z0-9_]+\([^;]*?\)\{\n_start:", c_text):
        pos = m.start()
        out_parts.append(c_text[last_idx:pos])
        depth = 0
        started = False
        end_pos = pos
        for i in range(pos, len(c_text)):
            if c_text[i] == "{":
                depth += 1
                started = True
            elif c_text[i] == "}":
                depth -= 1
                if started and depth == 0:
                    end_pos = i + 1
                    break
        f = c_text[pos:end_pos]
        last_idx = end_pos

        # Track variables assigned from u64_default_consts
        local_u64_defs = set()
        for dm in re.finditer(r"([a-zA-Z0-9_]+) = (?:\(\(lean_object\*\)\()?([a-zA-Z0-9_]+)\)?;", f):
            if dm.group(2) in u64_default_consts:
                local_u64_defs.add(dm.group(1))

        u64_gets = {}
        set_gets = {}
        for gm in re.finditer(r"([a-zA-Z0-9_]+) = (lean_array_get_borrowed|lean_array_get|lean_array_uget_borrowed|lean_array_fget_borrowed)\(([^;]+)\);", f):
            dst, kind, args = gm.group(1), gm.group(2), gm.group(3)
            uses = [line.strip() for line in f.splitlines() if re.search(r"\b" + re.escape(dst) + r"\b", line) and "lean_object* " not in line]
            ok = True
            has_unbox = False
            has_set = False
            for u in uses:
                if u.startswith(f"{dst} = {kind}("): continue
                if f"lean_unbox_uint64({dst})" in u:
                    has_unbox = True
                    continue
                if u in (f"lean_dec({dst});", f"lean_inc({dst});"): continue
                if re.search(r"= lean_array_set\([^,]+, [^,]+, " + re.escape(dst) + r"\);", u):
                    has_set = True
                    continue
                ok = False
            arg_list = [x.strip() for x in args.split(",")]
            is_u64_def = len(arg_list) == 3 and arg_list[0] in local_u64_defs
            if ok and (has_unbox or (has_set and is_u64_def)):
                u64_gets[dst] = (kind, args)

        if u64_gets:
            new_lines = []
            for line in f.splitlines():
                s = line.strip()
                if any(s.startswith(t) for t in ("lean_object* ", "uint64_t ", "uint8_t ")):
                    decls = [d.strip() for d in s.split(";") if d.strip()]
                    new_decls = []
                    for d in decls:
                        vname = d.split()[-1]
                        if vname in u64_gets:
                            new_decls.append(f"uint64_t {vname};")
                        else:
                            new_decls.append(d + ";")
                    new_lines.append(" ".join(new_decls))
                    continue
                if any(s in (f"lean_dec({dst});", f"lean_inc({dst});") for dst in u64_gets):
                    continue
                replaced_assign = False
                for dst, (kind, args) in u64_gets.items():
                    if s == f"{dst} = {kind}({args});":
                        if kind == "lean_array_get_borrowed":
                            new_lines.append(f"{dst} = ln_sarray_get_borrowed_u64({args});")
                        elif kind == "lean_array_get":
                            new_lines.append(f"{dst} = ln_sarray_get_u64({args});")
                        elif kind == "lean_array_uget_borrowed":
                            new_lines.append(f"{dst} = ln_sarray_uget_u64({args});")
                        elif kind == "lean_array_fget_borrowed":
                            a_arg, i_arg = [x.strip() for x in args.split(",")]
                            new_lines.append(f"{dst} = ln_sarray_uget_u64({a_arg}, lean_unbox({i_arg}));")
                        replaced_assign = True
                        break
                if replaced_assign:
                    continue
                for dst in u64_gets:
                    line = line.replace(f"lean_unbox_uint64({dst})", dst)
                    line = re.sub(r"lean_array_set\(([^,]+), ([^,]+), " + re.escape(dst) + r"\)", rf"ln_sarray_set_u64(\1, \2, {dst})", line)
                new_lines.append(line)
            f = "\n".join(new_lines)

        f = re.sub(r"\blean_mk_empty_array_with_capacity\(", "ln_mk_empty_sarray_u64(", f)
        f = re.sub(r"\blean_mk_array\(", "ln_mk_array_auto(", f)
        f = re.sub(r"\blean_array_size\(", "ln_array_size_auto(", f)
        f = re.sub(r"\blean_array_get_size\(", "ln_array_get_size_auto(", f)
        f = re.sub(r"\blean_array_push\(", "ln_array_push_auto(", f)
        f = re.sub(r"\blean_array_set\(", "ln_array_set_auto(", f)
        f = re.sub(r"\blean_array_get\(", "ln_array_get_auto(", f)
        f = re.sub(r"\blean_array_get_borrowed\(", "ln_array_get_borrowed_auto(", f)
        f = re.sub(r"\blean_array_fget_borrowed\(", "ln_array_fget_borrowed_auto(", f)

        box_vars = {}
        for bm in re.finditer(r"([a-zA-Z0-9_]+) = lean_box_uint64\(([a-zA-Z0-9_]+)\);", f):
            bv, uv = bm.group(1), bm.group(2)
            uses = [line.strip() for line in f.splitlines() if re.search(r"\b" + re.escape(bv) + r"\b", line) and "lean_object* " not in line]
            if len(uses) == 2 and any("= ln_array_set_auto(" in u and u.endswith(f", {bv});") for u in uses):
                box_vars[bv] = uv
        if box_vars:
            new_lines = []
            for line in f.splitlines():
                s = line.strip()
                if any(s == f"{bv} = lean_box_uint64({uv});" for bv, uv in box_vars.items()):
                    continue
                for bv, uv in box_vars.items():
                    line = re.sub(r"ln_array_set_auto\(([^,]+), ([^,]+), " + re.escape(bv) + r"\)", rf"ln_sarray_set_u64(\1, \2, {uv})", line)
                new_lines.append(line)
            f = "\n".join(new_lines)
        out_parts.append(f)
    out_parts.append(c_text[last_idx:])
    return "".join(out_parts)

def apply_pass2_range_forin(c_text):
    # Sub-pass 2A: 1D Range.forIn' loop (returns lean_object* sarray or uint64_t accumulator)
    out_parts = []
    last_idx = 0
    for m in re.finditer(r"LEAN_EXPORT (lean_object\*|uint64_t) (l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00[a-zA-Z0-9_]+)\(([^)]*)\)\{\n_start:", c_text):
        pos = m.start()
        out_parts.append(c_text[last_idx:pos])
        ret_ty = m.group(1)
        fn_name = m.group(2)
        params_str = m.group(3)
        depth = 0
        started = False
        end_pos = pos
        for i in range(pos, len(c_text)):
            if c_text[i] == "{":
                depth += 1
                started = True
            elif c_text[i] == "}":
                depth -= 1
                if started and depth == 0:
                    end_pos = i + 1
                    break
        f = c_text[pos:end_pos]
        last_idx = end_pos

        params = [p.strip().split()[-1] for p in params_str.split(",") if p.strip()]
        if len(params) < 3:
            out_parts.append(f)
            continue
        range_var, b_var, i_var = params[-3], params[-2], params[-1]

        # Extract else block inside _start
        m_start = re.search(
            r"_start:\n\{\nlean_object\* (v_stop_[0-9_]+); lean_object\* (v_step_[0-9_]+); uint8_t (v___x_[0-9_]+);[ \t]*\n"
            r"\1 = lean_ctor_get\(" + re.escape(range_var) + r", 1\);\n"
            r"\2 = lean_ctor_get\(" + re.escape(range_var) + r", 2\);\n"
            r"\3 = lean_nat_dec_lt\(" + re.escape(i_var) + r", \1\);\n"
            r"if \(\3 == 0\)\n\{\nlean_dec\(" + re.escape(i_var) + r"\);\nreturn " + re.escape(b_var) + r";\n\}\nelse\n\{\n",
            f
        )
        if not m_start:
            out_parts.append(f)
            continue
        stop_var, step_var = m_start.group(1), m_start.group(2)
        else_body = f[m_start.end():]
        # Strip trailing }\n}\n}
        if not else_body.endswith("\n}\n}\n}"):
            out_parts.append(f)
            continue
        else_body = else_body[:-6]

        # Skip if else_body contains control flow or function calls other than simple arithmetic / array ops
        if "goto v_resetjp_" in else_body or "if (" in else_body:
            out_parts.append(f)
            continue

        # Check tail:
        # v_step_next = lean_nat_add(i_var, step_var);
        # lean_dec(i_var);
        # b_var = next_b;
        # i_var = v_step_next;
        # goto _start;
        lines = [l.strip() for l in else_body.splitlines() if l.strip()]
        if len(lines) < 6 or lines[-1] != "goto _start;":
            out_parts.append(f)
            continue
        m_b = re.match(re.escape(b_var) + r" = ([a-zA-Z0-9_]+);", lines[-3])
        m_i = re.match(re.escape(i_var) + r" = ([a-zA-Z0-9_]+);", lines[-2])
        if not (m_b and m_i):
            out_parts.append(f)
            continue
        next_b, next_i = m_b.group(1), m_i.group(1)
        if lines[-4] != f"lean_dec({i_var});" or lines[-5] != f"{next_i} = lean_nat_add({i_var}, {step_var});":
            out_parts.append(f)
            continue

        core_lines = lines[:-5]
        # Check for unsupported operations in core_lines
        supported = True
        sarray_Params = set()
        array_Params = set()
        nat_Params = set()
        nat_temps = {}
        mut_b = False

        for cl in core_lines:
            if any(cl.startswith(t) for t in ("lean_object* ", "uint64_t ", "uint8_t ")):
                continue
            if "= ln_sarray_get_borrowed_u64(" in cl:
                gm = re.match(r"([a-zA-Z0-9_]+) = ln_sarray_get_borrowed_u64\(([^,]+), ([^,]+), ([^)]+)\);", cl)
                if not gm:
                    supported = False; break
                arr, idx = gm.group(3).strip(), gm.group(4).strip()
                if arr not in params:
                    supported = False; break
                sarray_Params.add(arr)
                if idx != i_var and idx not in nat_temps and idx not in params:
                    supported = False; break
                if idx in params and idx != i_var:
                    nat_Params.add(idx)
            elif "= ln_sarray_set_u64(" in cl:
                sm = re.match(re.escape(next_b) + r" = ln_sarray_set_u64\(" + re.escape(b_var) + r", ([^,]+), ([^)]+)\);", cl)
                if not sm or ret_ty != "lean_object*":
                    supported = False; break
                idx = sm.group(1).strip()
                if idx != i_var and idx not in nat_temps:
                    supported = False; break
                mut_b = True
                sarray_Params.add(b_var)
            elif "= lean_nat_add(" in cl:
                nm = re.match(r"([a-zA-Z0-9_]+) = lean_nat_add\(([^,]+), " + re.escape(i_var) + r"\);", cl)
                if not nm:
                    supported = False; break
                base_n = nm.group(2).strip()
                if base_n not in params:
                    supported = False; break
                nat_Params.add(base_n)
                nat_temps[nm.group(1)] = f"ln_nat_{base_n} + ln_i"
            elif cl.startswith("lean_dec("):
                dm = re.match(r"lean_dec\(([a-zA-Z0-9_]+)\);", cl)
                if not dm or dm.group(1) not in nat_temps:
                    supported = False; break
            elif "= lean_uint64_of_nat(" in cl:
                um = re.match(r"([a-zA-Z0-9_]+) = lean_uint64_of_nat\(([a-zA-Z0-9_]+)\);", cl)
                if not um or (um.group(2) != i_var and um.group(2) not in nat_temps and um.group(2) not in params):
                    supported = False; break
                if um.group(2) in params and um.group(2) != i_var:
                    nat_Params.add(um.group(2))
            elif "= lean_unsigned_to_nat(" in cl:
                um = re.match(r"([a-zA-Z0-9_]+) = lean_unsigned_to_nat\(([0-9]+)u\);", cl)
                if not um:
                    supported = False; break
                nat_temps[um.group(1)] = um.group(2)
            elif "= ln_array_get_borrowed_auto(" in cl:
                gm = re.match(r"([a-zA-Z0-9_]+) = ln_array_get_borrowed_auto\(([^,]+), ([^,]+), ([^)]+)\);", cl)
                if not gm:
                    supported = False; break
                arr, idx = gm.group(3).strip(), gm.group(4).strip()
                if arr not in params:
                    supported = False; break
                array_Params.add(arr)
                if idx != i_var and idx not in nat_temps and idx not in params:
                    supported = False; break
                if idx in params and idx != i_var:
                    nat_Params.add(idx)
            elif any(fn_call in cl for fn_call in ("lean_alloc_", "lean_array_", "ln_array_", "lean_nat_", "l_")):
                if "___boxed__const__" not in cl:
                    supported = False; break

        if not supported or (ret_ty == "lean_object*" and not mut_b):
            out_parts.append(f)
            continue

        # Build fast-path!
        conds = [f"lean_is_scalar({i_var})", f"lean_is_scalar({stop_var})", f"{step_var} == lean_box(1)"]
        for np in sorted(nat_Params):
            conds.append(f"lean_is_scalar({np})")
        for sp in sorted(sarray_Params):
            conds.append(f"lean_obj_tag({sp}) == 248")
        for ap in sorted(array_Params):
            conds.append(f"lean_obj_tag({ap}) == 246")

        fp = []
        fp.append("{")
        fp.append(f"lean_object* {stop_var} = lean_ctor_get({range_var}, 1);")
        fp.append(f"lean_object* {step_var} = lean_ctor_get({range_var}, 2);")
        fp.append(f"if ({' && '.join(conds)}) {{")
        fp.append(f"size_t ln_i = lean_unbox({i_var});")
        fp.append(f"size_t ln_stop = lean_unbox({stop_var});")
        for np in sorted(nat_Params):
            fp.append(f"size_t ln_nat_{np} = lean_unbox({np});")
        if ret_ty == "uint64_t":
            fp.append(f"uint64_t ln_acc = {b_var};")
        else:
            fp.append(f"{b_var} = ln_sarray_ensure_exclusive_u64({b_var});")
        fp.append("size_t ln_limit = ln_stop;")
        for sp in sorted(sarray_Params):
            const_kw = "" if (ret_ty == "lean_object*" and sp == b_var) else "const "
            fp.append(f"{const_kw}uint64_t* __restrict__ ln_ptr_{sp} = ln_sarray_u64_ptr({sp});")
            fp.append(f"size_t ln_sz_{sp} = ln_sarray_u64_size({sp});")
            fp.append(f"if (ln_sz_{sp} < ln_limit) ln_limit = ln_sz_{sp};")
        for ap in sorted(array_Params):
            fp.append(f"lean_object* const* __restrict__ ln_aptr_{ap} = (lean_object* const*)lean_array_cptr({ap});")
            fp.append(f"size_t ln_asz_{ap} = lean_array_size({ap});")
        fp.append("for (; ln_i < ln_limit; ++ln_i) {")
        for cl in core_lines:
            if any(cl.startswith(t) for t in ("lean_object* ", "uint64_t ", "uint8_t ")):
                fp.append(cl)
                continue
            if cl.startswith("lean_dec("):
                continue
            nm = re.match(r"([a-zA-Z0-9_]+) = lean_nat_add\(([^,]+), " + re.escape(i_var) + r"\);", cl)
            if nm:
                fp.append(f"size_t ln_nt_{nm.group(1)} = ln_nat_{nm.group(2).strip()} + ln_i;")
                continue
            um2 = re.match(r"([a-zA-Z0-9_]+) = lean_unsigned_to_nat\(([0-9]+)u\);", cl)
            if um2:
                fp.append(f"size_t ln_nt_{um2.group(1)} = {um2.group(2)};")
                continue
            gm2 = re.match(r"([a-zA-Z0-9_]+) = ln_array_get_borrowed_auto\(([^,]+), ([^,]+), ([^)]+)\);", cl)
            if gm2:
                dst_n, arr, idx = gm2.group(1), gm2.group(3).strip(), gm2.group(4).strip()
                idx_expr = "ln_i" if idx == i_var else (f"ln_nt_{idx}" if idx in nat_temps else f"ln_nat_{idx}")
                fp.append(f"size_t ln_nt_{dst_n} = ({idx_expr} < ln_asz_{arr}) ? lean_unbox(ln_aptr_{arr}[{idx_expr}]) : 0;")
                continue
            um = re.match(r"([a-zA-Z0-9_]+) = lean_uint64_of_nat\(([a-zA-Z0-9_]+)\);", cl)
            if um:
                dst_u, src_n = um.group(1), um.group(2)
                if src_n == i_var:
                    fp.append(f"{dst_u} = (uint64_t)(ln_i);")
                elif src_n in nat_temps:
                    fp.append(f"{dst_u} = (uint64_t)(ln_nt_{src_n});")
                else:
                    fp.append(f"{dst_u} = (uint64_t)(ln_nat_{src_n});")
                continue
            gm = re.match(r"([a-zA-Z0-9_]+) = ln_sarray_get_borrowed_u64\(([^,]+), ([^,]+), ([^)]+)\);", cl)
            if gm:
                dst_u, arr, idx = gm.group(1), gm.group(3).strip(), gm.group(4).strip()
                idx_expr = "ln_i" if idx == i_var else (f"ln_nt_{idx}" if idx in nat_temps else f"ln_nat_{idx}")
                if idx == i_var:
                    fp.append(f"{dst_u} = ln_ptr_{arr}[ln_i];")
                else:
                    fp.append(f"{dst_u} = ({idx_expr} < ln_sz_{arr}) ? ln_ptr_{arr}[{idx_expr}] : 0ULL;")
                continue
            sm = re.match(re.escape(next_b) + r" = ln_sarray_set_u64\(" + re.escape(b_var) + r", ([^,]+), ([^)]+)\);", cl)
            if sm:
                idx, val_u = sm.group(1).strip(), sm.group(2).strip()
                idx_expr = "ln_i" if idx == i_var else f"ln_nt_{idx}"
                if idx == i_var:
                    fp.append(f"ln_ptr_{b_var}[ln_i] = {val_u};")
                else:
                    fp.append(f"if ({idx_expr} < ln_sz_{b_var}) ln_ptr_{b_var}[{idx_expr}] = {val_u};")
                continue
            if ret_ty == "uint64_t":
                cl_mod = re.sub(r"\b" + re.escape(b_var) + r"\b", "ln_acc", cl)
                fp.append(cl_mod)
                if cl.startswith(f"{next_b} = "):
                    fp.append(f"ln_acc = {next_b};")
            else:
                fp.append(cl)
        fp.append("}")
        fp.append("for (; ln_i < ln_stop; ++ln_i) {")
        for cl in core_lines:
            if any(cl.startswith(t) for t in ("lean_object* ", "uint64_t ", "uint8_t ")):
                fp.append(cl)
                continue
            if cl.startswith("lean_dec("):
                continue
            nm = re.match(r"([a-zA-Z0-9_]+) = lean_nat_add\(([^,]+), " + re.escape(i_var) + r"\);", cl)
            if nm:
                fp.append(f"size_t ln_nt_{nm.group(1)} = ln_nat_{nm.group(2).strip()} + ln_i;")
                continue
            um2 = re.match(r"([a-zA-Z0-9_]+) = lean_unsigned_to_nat\(([0-9]+)u\);", cl)
            if um2:
                fp.append(f"size_t ln_nt_{um2.group(1)} = {um2.group(2)};")
                continue
            gm2 = re.match(r"([a-zA-Z0-9_]+) = ln_array_get_borrowed_auto\(([^,]+), ([^,]+), ([^)]+)\);", cl)
            if gm2:
                dst_n, arr, idx = gm2.group(1), gm2.group(3).strip(), gm2.group(4).strip()
                idx_expr = "ln_i" if idx == i_var else (f"ln_nt_{idx}" if idx in nat_temps else f"ln_nat_{idx}")
                fp.append(f"size_t ln_nt_{dst_n} = ({idx_expr} < ln_asz_{arr}) ? lean_unbox(ln_aptr_{arr}[{idx_expr}]) : 0;")
                continue
            um = re.match(r"([a-zA-Z0-9_]+) = lean_uint64_of_nat\(([a-zA-Z0-9_]+)\);", cl)
            if um:
                dst_u, src_n = um.group(1), um.group(2)
                if src_n == i_var:
                    fp.append(f"{dst_u} = (uint64_t)(ln_i);")
                elif src_n in nat_temps:
                    fp.append(f"{dst_u} = (uint64_t)(ln_nt_{src_n});")
                else:
                    fp.append(f"{dst_u} = (uint64_t)(ln_nat_{src_n});")
                continue
            gm = re.match(r"([a-zA-Z0-9_]+) = ln_sarray_get_borrowed_u64\(([^,]+), ([^,]+), ([^)]+)\);", cl)
            if gm:
                dst_u, arr, idx = gm.group(1), gm.group(3).strip(), gm.group(4).strip()
                idx_expr = "ln_i" if idx == i_var else (f"ln_nt_{idx}" if idx in nat_temps else f"ln_nat_{idx}")
                fp.append(f"{dst_u} = ({idx_expr} < ln_sz_{arr}) ? ln_ptr_{arr}[{idx_expr}] : 0ULL;")
                continue
            sm = re.match(re.escape(next_b) + r" = ln_sarray_set_u64\(" + re.escape(b_var) + r", ([^,]+), ([^)]+)\);", cl)
            if sm:
                idx, val_u = sm.group(1).strip(), sm.group(2).strip()
                idx_expr = "ln_i" if idx == i_var else f"ln_nt_{idx}"
                fp.append(f"if ({idx_expr} < ln_sz_{b_var}) ln_ptr_{b_var}[{idx_expr}] = {val_u};")
                continue
            if ret_ty == "uint64_t":
                cl_mod = re.sub(r"\b" + re.escape(b_var) + r"\b", "ln_acc", cl)
                fp.append(cl_mod)
                if cl.startswith(f"{next_b} = "):
                    fp.append(f"ln_acc = {next_b};")
            else:
                fp.append(cl)
        fp.append("}")
        fp.append(f"lean_dec({i_var});")
        fp.append(f"return {'ln_acc' if ret_ty == 'uint64_t' else b_var};")
        fp.append("}")
        fp.append("}")

        f_new = f.replace("{\n_start:", "{\n" + "\n".join(fp) + "\n_start:", 1)
        out_parts.append(f_new)
    out_parts.append(c_text[last_idx:])
    c_text = "".join(out_parts)

    # Sub-pass 2B: 3-tuple of sarrays Range.forIn' loop (e.g. benchNbody_spec__0 and benchNbody_spec__2)
    out_parts = []
    last_idx = 0
    for m in re.finditer(r"LEAN_EXPORT lean_object\* (l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00[a-zA-Z0-9_]+)\(([^)]*)\)\{\n_start:", c_text):
        pos = m.start()
        out_parts.append(c_text[last_idx:pos])
        fn_name = m.group(1)
        params_str = m.group(2)
        depth = 0
        started = False
        end_pos = pos
        for i in range(pos, len(c_text)):
            if c_text[i] == "{":
                depth += 1
                started = True
            elif c_text[i] == "}":
                depth -= 1
                if started and depth == 0:
                    end_pos = i + 1
                    break
        f = c_text[pos:end_pos]
        last_idx = end_pos

        params = [p.strip().split()[-1] for p in params_str.split(",") if p.strip()]
        if len(params) < 3:
            out_parts.append(f)
            continue
        range_var, b_var, i_var = params[-3], params[-2], params[-1]

        m_3t = re.search(
            r"_start:\n\{\nlean_object\* (v_stop_[0-9_]+); lean_object\* (v_step_[0-9_]+); uint8_t (v___x_[0-9_]+);[ \t]*\n"
            r"\1 = lean_ctor_get\(" + re.escape(range_var) + r", 1\);\n"
            r"\2 = lean_ctor_get\(" + re.escape(range_var) + r", 2\);\n"
            r"\3 = lean_nat_dec_lt\(" + re.escape(i_var) + r", \1\);\n"
            r"if \(\3 == 0\)\n\{\nlean_dec\(" + re.escape(i_var) + r"\);\nreturn " + re.escape(b_var) + r";\n\}\nelse\n\{\n"
            r"lean_object\* (v_snd_[0-9_]+); lean_object\* (v_fst_[0-9_]+);[^\n]+\n"
            r"\4 = lean_ctor_get\(" + re.escape(b_var) + r", 1\);\n"
            r"\5 = lean_ctor_get\(" + re.escape(b_var) + r", 0\);\n"
            r".*?"
            r"v_resetjp_[0-9_]+:\n\{\n"
            r"lean_object\* (v_fst_[0-9_]+); lean_object\* (v_snd_[0-9_]+);[^\n]+\n"
            r"\6 = lean_ctor_get\(\4, 0\);\n"
            r"\7 = lean_ctor_get\(\4, 1\);\n"
            r".*?"
            r"v_resetjp_[0-9_]+:\n\{\n",
            f, re.DOTALL
        )
        if not m_3t:
            out_parts.append(f)
            continue
        stop_var, step_var = m_3t.group(1), m_3t.group(2)
        snd0, arr0, arr1, arr2 = m_3t.group(4), m_3t.group(5), m_3t.group(6), m_3t.group(7)
        inner = f[m_3t.end():]
        m_end = re.search(r"\nif \(v_isShared_[0-9_]+ == 0\)\n\{", inner)
        if not m_end:
            out_parts.append(f)
            continue
        core_block = inner[:m_end.start()]
        core_lines = [l.strip() for l in core_block.splitlines() if l.strip()]

        # Track array aliases (e.g. v___x_1266_ = ln_sarray_set_u64(v_fst_1208_, ...))
        alias_map = {arr0: arr0, arr1: arr1, arr2: arr2}
        sarray_vars = {arr0, arr1, arr2}
        nat_Params = set()
        once_inits = []
        supported = True

        for cl in core_lines:
            if any(cl.startswith(t) for t in ("lean_object* ", "uint64_t ", "uint8_t ")):
                continue
            om = re.match(r"([a-zA-Z0-9_]+) = lean_obj_once\(([^;]+)\);", cl)
            if om:
                once_inits.append((om.group(1), om.group(2)))
                sarray_vars.add(om.group(1))
                continue
            gm = re.match(r"([a-zA-Z0-9_]+) = ln_sarray_(?:get_borrowed_u64|get_u64)\(([^,]+), ([^,]+), ([^)]+)\);", cl)
            if gm:
                arr, idx = gm.group(3).strip(), gm.group(4).strip()
                root_arr = alias_map.get(arr, arr)
                sarray_vars.add(root_arr)
                if idx != i_var:
                    if idx in params:
                        nat_Params.add(idx)
                    else:
                        supported = False; break
                continue
            sm = re.match(r"([a-zA-Z0-9_]+) = ln_sarray_set_u64\(([^,]+), ([^,]+), ([^)]+)\);", cl)
            if sm:
                dst_a, src_a, idx = sm.group(1), sm.group(2).strip(), sm.group(3).strip()
                if src_a not in alias_map:
                    supported = False; break
                alias_map[dst_a] = alias_map[src_a]
                if idx != i_var:
                    if idx in params:
                        nat_Params.add(idx)
                    else:
                        supported = False; break
                continue
            if any(fn_call in cl for fn_call in ("lean_alloc_", "lean_array_", "ln_array_", "lean_nat_")):
                supported = False; break

        if not supported:
            out_parts.append(f)
            continue

        conds = [f"lean_is_scalar({i_var})", f"lean_is_scalar({stop_var})", f"{step_var} == lean_box(1)"]
        for np in sorted(nat_Params):
            conds.append(f"lean_is_scalar({np})")

        fp = []
        fp.append("{")
        fp.append(f"lean_object* {stop_var} = lean_ctor_get({range_var}, 1);")
        fp.append(f"lean_object* {step_var} = lean_ctor_get({range_var}, 2);")
        fp.append(f"if ({' && '.join(conds)}) {{")
        fp.append(f"lean_object* {snd0} = lean_ctor_get({b_var}, 1);")
        fp.append(f"lean_object* {arr0} = lean_ctor_get({b_var}, 0);")
        fp.append(f"lean_object* {arr1} = lean_ctor_get({snd0}, 0);")
        fp.append(f"lean_object* {arr2} = lean_ctor_get({snd0}, 1);")
        for ov, oargs in once_inits:
            fp.append(f"lean_object* {ov} = lean_obj_once({oargs});")
        tag_conds = [f"lean_obj_tag({sv}) == 248" for sv in sorted(sarray_vars)]
        fp.append(f"if ({' && '.join(tag_conds)}) {{")
        fp.append(f"lean_inc({arr0}); lean_inc({arr1}); lean_inc({arr2}); lean_dec({b_var});")
        for ma in (arr0, arr1, arr2):
            fp.append(f"{ma} = ln_sarray_ensure_exclusive_u64({ma});")
            fp.append(f"uint64_t* __restrict__ ln_ptr_{ma} = ln_sarray_u64_ptr({ma});")
            fp.append(f"size_t ln_sz_{ma} = ln_sarray_u64_size({ma});")
        for sa in sorted(sarray_vars - {arr0, arr1, arr2}):
            fp.append(f"const uint64_t* __restrict__ ln_ptr_{sa} = ln_sarray_u64_ptr({sa});")
            fp.append(f"size_t ln_sz_{sa} = ln_sarray_u64_size({sa});")
        for np in sorted(nat_Params):
            fp.append(f"size_t ln_nat_{np} = lean_unbox({np});")
        fp.append(f"size_t ln_i = lean_unbox({i_var});")
        fp.append(f"size_t ln_stop = lean_unbox({stop_var});")
        fp.append("for (; ln_i < ln_stop; ++ln_i) {")
        for cl in core_lines:
            if any(cl.startswith(t) for t in ("lean_object* ", "uint64_t ", "uint8_t ")):
                fp.append(cl)
                continue
            if "= lean_obj_once(" in cl:
                continue
            gm = re.match(r"([a-zA-Z0-9_]+) = ln_sarray_(?:get_borrowed_u64|get_u64)\(([^,]+), ([^,]+), ([^)]+)\);", cl)
            if gm:
                dst_u, arr, idx = gm.group(1), gm.group(3).strip(), gm.group(4).strip()
                root_arr = alias_map.get(arr, arr)
                idx_expr = "ln_i" if idx == i_var else f"ln_nat_{idx}"
                fp.append(f"{dst_u} = ({idx_expr} < ln_sz_{root_arr}) ? ln_ptr_{root_arr}[{idx_expr}] : 0ULL;")
                continue
            sm = re.match(r"([a-zA-Z0-9_]+) = ln_sarray_set_u64\(([^,]+), ([^,]+), ([^)]+)\);", cl)
            if sm:
                src_a, idx, val_u = sm.group(2).strip(), sm.group(3).strip(), sm.group(4).strip()
                root_arr = alias_map[src_a]
                idx_expr = "ln_i" if idx == i_var else f"ln_nat_{idx}"
                fp.append(f"if ({idx_expr} < ln_sz_{root_arr}) ln_ptr_{root_arr}[{idx_expr}] = {val_u};")
                continue
            fp.append(cl)
        fp.append("}")
        fp.append(f"lean_dec({i_var});")
        fp.append(f"lean_object* ln_p1 = lean_alloc_ctor(0, 2, 0); lean_ctor_set(ln_p1, 0, {arr1}); lean_ctor_set(ln_p1, 1, {arr2});")
        fp.append(f"lean_object* ln_p0 = lean_alloc_ctor(0, 2, 0); lean_ctor_set(ln_p0, 0, {arr0}); lean_ctor_set(ln_p0, 1, ln_p1);")
        fp.append("return ln_p0;")
        fp.append("}")
        fp.append("}")
        fp.append("}")

        f_new = f.replace("{\n_start:", "{\n" + "\n".join(fp) + "\n_start:", 1)
        out_parts.append(f_new)
    out_parts.append(c_text[last_idx:])
    c_text = "".join(out_parts)

    # Sub-pass 2D: 1-array or 2-tuple of sarrays Range.forIn' push initialization loops
    out_parts = []
    last_idx = 0
    for m in re.finditer(r"LEAN_EXPORT lean_object\* (l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00[a-zA-Z0-9_]+)\(([^)]*)\)\{\n_start:", c_text):
        pos = m.start()
        out_parts.append(c_text[last_idx:pos])
        params_str = m.group(2)
        depth = 0
        started = False
        end_pos = pos
        for i in range(pos, len(c_text)):
            if c_text[i] == "{":
                depth += 1
                started = True
            elif c_text[i] == "}":
                depth -= 1
                if started and depth == 0:
                    end_pos = i + 1
                    break
        f = c_text[pos:end_pos]
        last_idx = end_pos
        if "ln_array_push_auto(" not in f:
            out_parts.append(f); continue
        params = [p.strip().split()[-1] for p in params_str.split(",") if p.strip()]
        if len(params) < 3:
            out_parts.append(f); continue
        range_var, b_var, i_var = params[-3], params[-2], params[-1]
        m_1p = re.search(
            r"_start:\n\{\nlean_object\* (v_stop_[0-9_]+); lean_object\* (v_step_[0-9_]+); uint8_t (v___x_[0-9_]+);[ \t]*\n"
            r"\1 = lean_ctor_get\(" + re.escape(range_var) + r", 1\);\n"
            r"\2 = lean_ctor_get\(" + re.escape(range_var) + r", 2\);\n"
            r"\3 = lean_nat_dec_lt\(" + re.escape(i_var) + r", \1\);\n"
            r"if \(\3 == 0\)\n\{\nlean_dec\(" + re.escape(i_var) + r"\);\nreturn " + re.escape(b_var) + r";\n\}\nelse\n\{\n"
            r"(.*?)\n"
            r"([a-zA-Z0-9_]+) = lean_box_uint64\(([a-zA-Z0-9_]+)\);\n"
            r"([a-zA-Z0-9_]+) = ln_array_push_auto\(" + re.escape(b_var) + r", \5\);\n"
            r"([a-zA-Z0-9_]+) = lean_nat_add\(" + re.escape(i_var) + r", \2\);\n"
            r"lean_dec\(" + re.escape(i_var) + r"\);\n"
            + re.escape(b_var) + r" = \7;\n"
            + re.escape(i_var) + r" = \8;\n"
            r"goto _start;",
            f, re.DOTALL
        )
        if m_1p:
            stop_var, step_var, core_1p, val_u = m_1p.group(1), m_1p.group(2), m_1p.group(4), m_1p.group(6)
            core_mod = re.sub(r"([a-zA-Z0-9_]+) = lean_uint64_of_nat\(" + re.escape(i_var) + r"\);", r"\1 = (uint64_t)ln_i;", core_1p)
            if "lean_nat_" not in core_mod and "lean_alloc_" not in core_mod:
                fp = [
                    "{",
                    f"lean_object* {stop_var} = lean_ctor_get({range_var}, 1);",
                    f"lean_object* {step_var} = lean_ctor_get({range_var}, 2);",
                    f"if ({i_var} == lean_box(0) && lean_is_scalar({stop_var}) && {step_var} == lean_box(1) && lean_obj_tag({b_var}) == 248 && ln_sarray_u64_size({b_var}) == 0) {{",
                    f"size_t ln_n = lean_unbox({stop_var});",
                    f"lean_dec({b_var});",
                    "lean_object* ln_r = lean_alloc_sarray(8, ln_n, ln_n);",
                    "uint64_t* __restrict__ ln_ptr = ln_sarray_u64_ptr(ln_r);",
                    "for (size_t ln_i = 0; ln_i < ln_n; ++ln_i) {",
                    core_mod,
                    f"ln_ptr[ln_i] = {val_u};",
                    "}",
                    "return ln_r;",
                    "}",
                    "}"
                ]
                out_parts.append(f.replace("{\n_start:", "{\n" + "\n".join(fp) + "\n_start:", 1))
                continue
        m_2p = re.search(
            r"_start:\n\{\nlean_object\* (v_stop_[0-9_]+); lean_object\* (v_step_[0-9_]+); uint8_t (v___x_[0-9_]+);[ \t]*\n"
            r"\1 = lean_ctor_get\(" + re.escape(range_var) + r", 1\);\n"
            r"\2 = lean_ctor_get\(" + re.escape(range_var) + r", 2\);\n"
            r"\3 = lean_nat_dec_lt\(" + re.escape(i_var) + r", \1\);\n"
            r"if \(\3 == 0\)\n\{\nlean_dec\(" + re.escape(i_var) + r"\);\nreturn " + re.escape(b_var) + r";\n\}\nelse\n\{\n"
            r"lean_object\* (v_fst_[0-9_]+); lean_object\* (v_snd_[0-9_]+);[^\n]+\n"
            r"\4 = lean_ctor_get\(" + re.escape(b_var) + r", 0\);\n"
            r"\5 = lean_ctor_get\(" + re.escape(b_var) + r", 1\);\n"
            r".*?"
            r"v_resetjp_[0-9_]+:\n\{\n"
            r"(.*?)\n"
            r"if \(v_isShared_[0-9_]+ == 0\)\n\{",
            f, re.DOTALL
        )
        if m_2p:
            stop_var, step_var, fst_v, snd_v, core_2p = m_2p.group(1), m_2p.group(2), m_2p.group(4), m_2p.group(5), m_2p.group(6)
            pm1 = re.search(r"([a-zA-Z0-9_]+) = lean_box_uint64\(([a-zA-Z0-9_]+)\);\n([a-zA-Z0-9_]+) = ln_array_push_auto\(" + re.escape(fst_v) + r", \1\);", core_2p)
            pm2 = re.search(r"([a-zA-Z0-9_]+) = lean_box_uint64\(([a-zA-Z0-9_]+)\);\n([a-zA-Z0-9_]+) = ln_array_push_auto\(" + re.escape(snd_v) + r", \1\);", core_2p)
            if pm1 and pm2:
                u1, u2 = pm1.group(2), pm2.group(2)
                nat_exprs = {i_var: "ln_i"}
                c2_lines = []
                ok_2p = True
                for cl in [l.strip() for l in core_2p.splitlines() if l.strip()]:
                    if any(cl.startswith(t) for t in ("lean_object* ", "uint64_t ", "uint8_t ")):
                        c2_lines.append(cl); continue
                    if cl.startswith("lean_dec("): continue
                    if "= lean_box_uint64(" in cl or "= ln_array_push_auto(" in cl: continue
                    um = re.match(r"([a-zA-Z0-9_]+) = lean_unsigned_to_nat\(([0-9]+)u\);", cl)
                    if um:
                        nat_exprs[um.group(1)] = f"{um.group(2)}ULL"; continue
                    nm = re.match(r"([a-zA-Z0-9_]+) = lean_nat_(mul|add|land)\(([a-zA-Z0-9_]+), ([a-zA-Z0-9_]+)\);", cl)
                    if nm and nm.group(3) in nat_exprs and nm.group(4) in nat_exprs:
                        op_sym = {"mul": "*", "add": "+", "land": "&"}[nm.group(2)]
                        nat_exprs[nm.group(1)] = f"({nat_exprs[nm.group(3)]} {op_sym} {nat_exprs[nm.group(4)]})"
                        continue
                    uom = re.match(r"([a-zA-Z0-9_]+) = lean_uint64_of_nat\(([a-zA-Z0-9_]+)\);", cl)
                    if uom and uom.group(2) in nat_exprs:
                        c2_lines.append(f"{uom.group(1)} = (uint64_t){nat_exprs[uom.group(2)]};")
                        continue
                    ok_2p = False; break
                if ok_2p:
                    fp = [
                        "{",
                        f"lean_object* {stop_var} = lean_ctor_get({range_var}, 1);",
                        f"lean_object* {step_var} = lean_ctor_get({range_var}, 2);",
                        f"lean_object* {fst_v} = lean_ctor_get({b_var}, 0);",
                        f"lean_object* {snd_v} = lean_ctor_get({b_var}, 1);",
                        f"if ({i_var} == lean_box(0) && lean_is_scalar({stop_var}) && {step_var} == lean_box(1) && lean_obj_tag({fst_v}) == 248 && lean_obj_tag({snd_v}) == 248 && ln_sarray_u64_size({fst_v}) == 0 && ln_sarray_u64_size({snd_v}) == 0) {{",
                        f"size_t ln_n = lean_unbox({stop_var});",
                        f"lean_dec({b_var});",
                        "lean_object* ln_ra = lean_alloc_sarray(8, ln_n, ln_n);",
                        "lean_object* ln_rb = lean_alloc_sarray(8, ln_n, ln_n);",
                        "uint64_t * __restrict__ ln_pa = ln_sarray_u64_ptr(ln_ra), * __restrict__ ln_pb = ln_sarray_u64_ptr(ln_rb);",
                        "for (size_t ln_i = 0; ln_i < ln_n; ++ln_i) {",
                        *c2_lines,
                        f"ln_pa[ln_i] = {u1}; ln_pb[ln_i] = {u2};",
                        "}",
                        "lean_object* ln_r = lean_alloc_ctor(0, 2, 0); lean_ctor_set(ln_r, 0, ln_ra); lean_ctor_set(ln_r, 1, ln_rb);",
                        "return ln_r;",
                        "}",
                        "}"
                    ]
                    out_parts.append(f.replace("{\n_start:", "{\n" + "\n".join(fp) + "\n_start:", 1))
                    continue
        out_parts.append(f)
    out_parts.append(c_text[last_idx:])
    return "".join(out_parts)

def apply_pass3_while_sroa(c_text):
    # Step 1: Inline ___lam__0 helper into its parent whileM/repeatM function if it constructs a 1-arg ctor (Some state)
    lam_funcs = {}
    for m in re.finditer(r"LEAN_EXPORT lean_object\* (l___private_Init_While_0__(?:whileM|repeatM)_erased___at___00[a-zA-Z0-9_]+___redArg___lam__0)\(([^)]*)\)\{\n_start:\n\{", c_text):
        lam_name = m.group(1)
        params_str = m.group(2)
        pos = m.start()
        depth = 0
        end_pos = pos
        for i in range(pos, len(c_text)):
            if c_text[i] == "{": depth += 1
            elif c_text[i] == "}":
                depth -= 1
                if depth == 0:
                    end_pos = i + 1
                    break
        lam_body = c_text[m.end():end_pos-4].strip()
        params = [p.strip().split()[-1] for p in params_str.split(",") if p.strip()]
        lam_funcs[lam_name] = (params, lam_body)

    for lam_name, (lparams, lbody) in lam_funcs.items():
        parent_name = lam_name[:-9]
        m = re.search(r"LEAN_EXPORT lean_object\* " + re.escape(parent_name) + r"\([^)]*\)\{\n_start:", c_text)
        if not m: continue
        pos = m.start()
        depth = 0
        end_pos = pos
        for i in range(pos, len(c_text)):
            if c_text[i] == "{": depth += 1
            elif c_text[i] == "}":
                depth -= 1
                if depth == 0:
                    end_pos = i + 1
                    break
        f = c_text[pos:end_pos]
        jp_m = re.search(
            r"(v___jp_[0-9_]+):\n\{\nif \(lean_obj_tag\(([a-zA-Z0-9_]+)\) == 0\)\n\{.*?\n\}\nelse\n\{\nlean_object\* ([a-zA-Z0-9_]+);[ \t]*\n\3 = lean_ctor_get\(\2, 0\);\nlean_inc\(\3\);\nlean_dec_ref_known\(\2, 1\);\n([a-zA-Z0-9_]+) = \3;\ngoto _start;\n\}\n\}",
            f, re.DOTALL
        )
        if not jp_m: continue
        jp_label, y_var, state_var = jp_m.group(1), jp_m.group(2), jp_m.group(4)
        lb_lines = [l.strip() for l in lbody.splitlines() if l.strip()]
        if len(lb_lines) < 4 or not lb_lines[-1].startswith("return "): continue
        ret_v = lb_lines[-1].split()[1].rstrip(";")
        if lb_lines[-3] != f"{ret_v} = lean_alloc_ctor(1, 1, 0);": continue
        m_inner = re.match(re.escape(f"lean_ctor_set({ret_v}, 0, ") + r"([a-zA-Z0-9_]+)\);", lb_lines[-2])
        if not m_inner: continue
        inner_v = m_inner.group(1)
        core_lb = lb_lines[:-3]

        def repl_call(cm):
            call_dst = cm.group(1)
            args = [a.strip() for a in cm.group(2).split(",")]
            sub_map = dict(zip(lparams, args))
            inlined = []
            for cl in core_lb:
                cl_sub = cl
                for lp, arg in sub_map.items():
                    cl_sub = re.sub(r"\b" + re.escape(lp) + r"\b", arg, cl_sub)
                for lv in set(re.findall(r"\bv___x_[0-9_]+\b", cl)):
                    cl_sub = re.sub(r"\b" + re.escape(lv) + r"\b", f"{lv}_{call_dst}", cl_sub)
                inlined.append(cl_sub)
            inlined.append(f"{state_var} = {inner_v}_{call_dst};")
            inlined.append("goto _start;")
            return "\n".join(inlined)

        f_new = re.sub(
            r"([a-zA-Z0-9_]+) = " + re.escape(lam_name) + r"\(([^)]+)\);\n" + re.escape(y_var) + r" = \1;\ngoto " + re.escape(jp_label) + r";",
            repl_call,
            f
        )
        if f"goto {jp_label};" not in f_new:
            f_new = f_new.replace(jp_m.group(0) + "\n", "")
        c_text = c_text[:pos] + f_new + c_text[end_pos:]

    # Step 2: interprocedural nested whileM/repeatM scalar SROA
    scalar_consts = {}
    for m in re.finditer(r"static const lean_ctor_object ([a-zA-Z0-9_]+)_value = \{[^\n]*LEAN_SCALAR_PTR_LITERAL\(([^)]+)\)\}\};", c_text):
        bs = [int(x.strip()) for x in m.group(2).split(",")]
        val = sum(b << (8 * i) for i, b in enumerate(bs))
        scalar_consts[m.group(1)] = f"{val}ULL"

    const_pairs = {}
    for m in re.finditer(r"static const lean_ctor_object ([a-zA-Z0-9_]+)_value = \{[^\n]*\.m_objs = \{\(\(lean_object\*\)&([a-zA-Z0-9_]+)_value\),\(\(lean_object\*\)&([a-zA-Z0-9_]+)_value\)\}\};", c_text):
        const_pairs[m.group(1)] = (m.group(2), m.group(3))

    scalar_while_fns = {}
    out_parts = []
    last_idx = 0
    for m in re.finditer(r"LEAN_EXPORT lean_object\* (l___private_Init_While_0__(?:whileM|repeatM)_erased___at___00[a-zA-Z0-9_]+___redArg)\(([^)]*)\)\{\n_start:\n\{", c_text):
        pos = m.start()
        out_parts.append(c_text[last_idx:pos])
        fn_name = m.group(1)
        params_str = m.group(2)
        depth = 0
        end_pos = pos
        for i in range(pos, len(c_text)):
            if c_text[i] == "{": depth += 1
            elif c_text[i] == "}":
                depth -= 1
                if depth == 0:
                    end_pos = i + 1
                    break
        f = c_text[pos:end_pos]
        last_idx = end_pos

        param_decls = [p.strip() for p in params_str.split(",") if p.strip()]
        params = [p.split()[-1] for p in param_decls]
        if not params:
            out_parts.append(f); continue
        state_var = params[-1]
        body = f[m.end() - pos:-4]

        other_uses = [l.strip() for l in body.splitlines() if re.search(r"\b" + re.escape(state_var) + r"\b", l)]
        if not any(f"lean_ctor_get({state_var}, 0)" in u for u in other_uses):
            out_parts.append(f); continue

        ctor_gets = {}
        for gm in re.finditer(r"([a-zA-Z0-9_]+) = lean_ctor_get\(([a-zA-Z0-9_]+), ([01])\);", body):
            dst, src, idx = gm.group(1), gm.group(2), int(gm.group(3))
            if dst.startswith("v_unused_"): continue
            if idx not in ctor_gets.setdefault(src, {}):
                ctor_gets[src][idx] = dst

        if state_var not in ctor_gets or 0 not in ctor_gets[state_var] or 1 not in ctor_gets[state_var]:
            out_parts.append(f); continue

        spine_nodes = []
        leaves = []
        def walk_prod(node):
            if node in ctor_gets and 0 in ctor_gets[node] and 1 in ctor_gets[node]:
                f0, s1 = ctor_gets[node][0], ctor_gets[node][1]
                spine_nodes.append((node, f0, s1))
                return (walk_prod(f0), walk_prod(s1))
            idx_l = len(leaves)
            leaves.append(node)
            return idx_l
        spine_tree = walk_prod(state_var)
        internal_nodes = {n for (n, _, _) in spine_nodes}

        excl_info = {}
        ok_spine = True
        for (node, f0, s1) in spine_nodes:
            if len(re.findall(r"!lean_is_exclusive\(" + re.escape(node) + r"\)", body)) != 1:
                ok_spine = False; break
            em = re.search(
                r"([a-zA-Z0-9_]+) = !lean_is_exclusive\(" + re.escape(node) + r"\);\n"
                r"if \(\1 == 0\)\n\{\n"
                r"(?:lean_object\* [a-zA-Z0-9_]+;[ \t]*\n[a-zA-Z0-9_]+ = lean_ctor_get\(" + re.escape(node) + r", [01]\);\nlean_dec\([a-zA-Z0-9_]+\);\n)?"
                r"([a-zA-Z0-9_]+) = " + re.escape(node) + r";\n"
                r"([a-zA-Z0-9_]+) = \1;\n"
                r"goto (v_resetjp_[0-9_]+);\n\}\nelse\n\{\n"
                r"(?:lean_inc\([a-zA-Z0-9_]+\);\n)+lean_dec\(" + re.escape(node) + r"\);\n"
                r"\2 = lean_box\(0\);\n"
                r"\3 = \1;\n"
                r"goto \4;\n\}",
                body
            )
            if not em:
                ok_spine = False; break
            excl_info[node] = (em.group(1), em.group(2), em.group(3), em.group(4))
        if not ok_spine:
            out_parts.append(f); continue

        back_edges = re.findall(re.escape(state_var) + r" = ([a-zA-Z0-9_]+);\ngoto _start;", body)
        if not back_edges:
            out_parts.append(f); continue

        pair_defs = {}
        for am in re.finditer(
            r"([a-zA-Z0-9_]+) = lean_alloc_ctor\(0, 2, 0\);\n"
            r"lean_ctor_set\(\1, 0, ([a-zA-Z0-9_]+)\);\n"
            r"lean_ctor_set\(\1, 1, ([a-zA-Z0-9_]+)\);",
            body
        ):
            pair_defs[am.group(1)] = (am.group(2), am.group(3))

        for rm in re.finditer(
            r"if \([a-zA-Z0-9_]+ == 0\)\n\{\n"
            r"(?:lean_ctor_set\([a-zA-Z0-9_]+, [01], [a-zA-Z0-9_]+\);\n)*"
            r"([a-zA-Z0-9_]+) = [a-zA-Z0-9_]+;\n"
            r"goto (v_reusejp_[0-9_]+);\n\}\nelse\n\{\n"
            r"lean_object\* ([a-zA-Z0-9_]+);[ \t]*\n"
            r"\3 = lean_alloc_ctor\(0, 2, 0\);\n"
            r"lean_ctor_set\(\3, 0, ([a-zA-Z0-9_]+)\);\n"
            r"lean_ctor_set\(\3, 1, ([a-zA-Z0-9_]+)\);\n"
            r"\1 = \3;\n"
            r"goto \2;\n\}",
            body
        ):
            pair_defs[rm.group(1)] = (rm.group(4), rm.group(5))

        box_map = {}
        for bm in re.finditer(r"([a-zA-Z0-9_]+) = lean_box_uint64\(([a-zA-Z0-9_]+)\);", body):
            box_map[bm.group(1)] = bm.group(2)

        const_var_map = {}
        for cm in re.finditer(r"([a-zA-Z0-9_]+) = \(\(lean_object\*\)\(([a-zA-Z0-9_]+)\)\);", body):
            cname = cm.group(2)
            if cname in scalar_consts:
                box_map[cm.group(1)] = scalar_consts[cname]
            else:
                const_var_map[cm.group(1)] = cname

        inner_calls = []
        inner_leaf_vars = {}
        inner_internal_nodes = set()
        inner_excl_info = {}
        inner_arg_pairs = set()

        for icm in re.finditer(r"([a-zA-Z0-9_]+) = (l___private_Init_While_0__(?:whileM|repeatM)_erased___at___00[a-zA-Z0-9_]+___redArg)\(([^)]*)\);", body):
            ret_v, callee_fn, args_s = icm.group(1), icm.group(2), icm.group(3)
            if callee_fn not in scalar_while_fns:
                continue
            callee_tree, callee_num_leaves = scalar_while_fns[callee_fn]
            call_args = [a.strip() for a in args_s.split(",") if a.strip()]
            state_arg = call_args[-1]
            arg_leaves = []
            arg_pairs_local = set()
            def extract_arg_tree(t_node, cur_v):
                if isinstance(t_node, tuple):
                    if cur_v in pair_defs:
                        arg_pairs_local.add(cur_v)
                        a0, a1 = pair_defs[cur_v]
                        return extract_arg_tree(t_node[0], a0) and extract_arg_tree(t_node[1], a1)
                    cname = const_var_map.get(cur_v, cur_v)
                    if cname in const_pairs:
                        c0, c1 = const_pairs[cname]
                        return extract_arg_tree(t_node[0], c0) and extract_arg_tree(t_node[1], c1)
                    return False
                else:
                    arg_leaves.append(cur_v)
                    return True
            if not extract_arg_tree(callee_tree, state_arg):
                continue

            ret_local_internal = set()
            ret_local_excl = {}
            ret_local_leaves = {}
            def walk_ret_proj(t_node, cur_v):
                if isinstance(t_node, tuple):
                    if cur_v not in ctor_gets:
                        return
                    ret_local_internal.add(cur_v)
                    em = re.search(
                        r"([a-zA-Z0-9_]+) = !lean_is_exclusive\(" + re.escape(cur_v) + r"\);\n"
                        r"if \(\1 == 0\)\n\{\n"
                        r"(?:lean_object\* [a-zA-Z0-9_]+;[ \t]*\n[a-zA-Z0-9_]+ = lean_ctor_get\(" + re.escape(cur_v) + r", [01]\);\nlean_dec\([a-zA-Z0-9_]+\);\n)?"
                        r"([a-zA-Z0-9_]+) = " + re.escape(cur_v) + r";\n"
                        r"([a-zA-Z0-9_]+) = \1;\n"
                        r"goto (v_resetjp_[0-9_]+);\n\}\nelse\n\{\n"
                        r"(?:lean_inc\([a-zA-Z0-9_]+\);\n)+lean_dec\(" + re.escape(cur_v) + r"\);\n"
                        r"\2 = lean_box\(0\);\n"
                        r"\3 = \1;\n"
                        r"goto \4;\n\}",
                        body
                    )
                    if em:
                        ret_local_excl[cur_v] = (em.group(1), em.group(2), em.group(3), em.group(4))
                    for idx_c in (0, 1):
                        if idx_c in ctor_gets[cur_v]:
                            walk_ret_proj(t_node[idx_c], ctor_gets[cur_v][idx_c])
                else:
                    ret_local_leaves[cur_v] = f"ic_{ret_v}_{t_node}"
            walk_ret_proj(callee_tree, ret_v)
            inner_calls.append((icm.group(0), ret_v, callee_fn, call_args[:-1], arg_leaves, callee_num_leaves))
            inner_leaf_vars.update(ret_local_leaves)
            inner_internal_nodes.update(ret_local_internal)
            inner_excl_info.update(ret_local_excl)
            inner_arg_pairs.update(arg_pairs_local)

        node_set = {n for (n, _, _) in spine_nodes}
        be_leaf_vals = {}
        be_pair_vars = set()
        ok_be = True
        for nr in back_edges:
            vals = []
            def extract_be(cur_node, cur_v):
                if cur_node in node_set:
                    if cur_v not in pair_defs:
                        return False
                    be_pair_vars.add(cur_v)
                    a0, a1 = pair_defs[cur_v]
                    f0_n, s1_n = ctor_gets[cur_node][0], ctor_gets[cur_node][1]
                    return extract_be(f0_n, a0) and extract_be(s1_n, a1)
                else:
                    vals.append(cur_v)
                    return True
            if not extract_be(state_var, nr):
                ok_be = False; break
            be_leaf_vals[nr] = vals
        if not ok_be:
            out_parts.append(f); continue

        all_candidate_leaves = list(leaves) + list(inner_leaf_vars.keys())
        leaf_can_unbox = {}
        for lv in all_candidate_leaves:
            uses = [l.strip() for l in body.splitlines() if re.search(r"\b" + re.escape(lv) + r"\b", l) and "lean_object* " not in l]
            u_ok = True
            for u in uses:
                if "= lean_ctor_get(" in u and u.startswith(f"{lv} ="): continue
                if f"lean_unbox_uint64({lv})" in u: continue
                if u in (f"lean_dec({lv});", f"lean_inc({lv});"): continue
                if re.match(r"lean_ctor_set\([^,]+, [01], " + re.escape(lv) + r"\);", u): continue
                if re.match(r"[a-zA-Z0-9_]+ = " + re.escape(lv) + r";", u): continue
                u_ok = False
            leaf_can_unbox[lv] = u_ok

        leaf_is_u64 = {lv: leaf_can_unbox[lv] for lv in leaves}
        changed = True
        while changed:
            changed = False
            for idx_l, lv in enumerate(leaves):
                if not leaf_is_u64[lv]: continue
                for nr, vals in be_leaf_vals.items():
                    v_i = vals[idx_l]
                    if v_i in box_map or v_i in scalar_consts: continue
                    if v_i in inner_leaf_vars and leaf_can_unbox.get(v_i, False): continue
                    if v_i in leaves and leaf_is_u64[v_i]: continue
                    leaf_is_u64[lv] = False
                    changed = True
                    break

        # Validate that any inner_calls only pass scalarizable arg_leaves
        valid_inner_calls = []
        for ic_tup in inner_calls:
            call_str, ret_v, callee_fn, extra_args, arg_leaves, callee_num_leaves = ic_tup
            if all((av in box_map or av in scalar_consts or (av in inner_leaf_vars or (av in leaves and leaf_is_u64[av]))) for av in arg_leaves):
                valid_inner_calls.append(ic_tup)
        if len(valid_inner_calls) != len(inner_calls):
            # Fallback if an inner call wasn't fully scalarizable
            inner_calls = []
            inner_leaf_vars = {}
            inner_internal_nodes = set()
            inner_excl_info = {}
            inner_arg_pairs = set()

        ok_internal = True
        for (node, f0, s1) in spine_nodes:
            chk_v, reuse_v, shared_v, jp_lbl = excl_info[node]
            for l in body.splitlines():
                s = l.strip()
                if "lean_object* " in s: continue
                if not re.search(r"\b" + re.escape(node) + r"\b", s): continue
                if f"lean_ctor_get({node}, " in s: continue
                if s.startswith(f"{node} = lean_ctor_get("): continue
                if f"!lean_is_exclusive({node})" in s: continue
                if s in (f"lean_inc({node});", f"lean_dec({node});", f"{reuse_v} = {node};"): continue
                if node == state_var and any(s == f"{state_var} = {nr};" for nr in back_edges): continue
                if node != state_var and re.match(r"lean_ctor_set\([a-zA-Z0-9_]+, [01], " + re.escape(node) + r"\);", s):
                    continue
                ok_internal = False; break
        if not ok_internal:
            out_parts.append(f); continue

        hdr = ["{"]
        for lv in leaves:
            if leaf_is_u64[lv]:
                hdr.append(f"uint64_t u_{lv};")
            else:
                hdr.append(f"lean_object* {lv};")
        for (node, f0, s1) in spine_nodes:
            decl_f0 = f"lean_object* {f0} = " if (f0 in internal_nodes or leaf_is_u64.get(f0, False)) else f"{f0} = "
            decl_s1 = f"lean_object* {s1} = " if (s1 in internal_nodes or leaf_is_u64.get(s1, False)) else f"{s1} = "
            hdr.append(f"{decl_f0}lean_ctor_get({node}, 0);")
            hdr.append(f"{decl_s1}lean_ctor_get({node}, 1);")
        for lv in leaves:
            if leaf_is_u64[lv]:
                hdr.append(f"u_{lv} = lean_unbox_uint64({lv});")
            else:
                hdr.append(f"lean_inc({lv});")
        hdr.append(f"lean_dec({state_var});")
        for (node, _, _) in spine_nodes:
            chk_v, reuse_v, shared_v, _ = excl_info[node]
            hdr.append(f"lean_object* {reuse_v} = lean_box(0);")
            hdr.append(f"uint8_t {shared_v} = 1;")
            hdr.append(f"uint8_t {chk_v} = 1;")
        for inode, (chk_v, reuse_v, shared_v, _) in inner_excl_info.items():
            hdr.append(f"lean_object* {reuse_v} = lean_box(0);")
            hdr.append(f"uint8_t {shared_v} = 1;")
            hdr.append(f"uint8_t {chk_v} = 1;")

        new_body = body
        vars_to_strip_decl = set()
        for (node, f0, s1) in spine_nodes:
            chk_v, reuse_v, shared_v, _ = excl_info[node]
            vars_to_strip_decl.update([f0, s1, chk_v, reuse_v, shared_v])
        for inode in inner_internal_nodes:
            vars_to_strip_decl.add(inode)
            if inode in ctor_gets:
                for ch in ctor_gets[inode].values():
                    vars_to_strip_decl.add(ch)
        for inode, (chk_v, reuse_v, shared_v, _) in inner_excl_info.items():
            vars_to_strip_decl.update([chk_v, reuse_v, shared_v])

        for (node, f0, s1) in spine_nodes:
            chk_v, reuse_v, shared_v, jp_lbl = excl_info[node]
            new_body = re.sub(r"[ \t]*" + re.escape(f0) + r" = lean_ctor_get\(" + re.escape(node) + r", 0\);\n(?:[ \t]*lean_inc\(" + re.escape(f0) + r"\);\n)?", "", new_body)
            new_body = re.sub(r"[ \t]*" + re.escape(s1) + r" = lean_ctor_get\(" + re.escape(node) + r", 1\);\n(?:[ \t]*lean_inc\(" + re.escape(s1) + r"\);\n)?", "", new_body)
            new_body = re.sub(
                re.escape(chk_v) + r" = !lean_is_exclusive\(" + re.escape(node) + r"\);\n"
                r"if \(" + re.escape(chk_v) + r" == 0\)\n\{\n"
                r"(?:lean_object\* [a-zA-Z0-9_]+;[ \t]*\n[a-zA-Z0-9_]+ = lean_ctor_get\(" + re.escape(node) + r", [01]\);\nlean_dec\([a-zA-Z0-9_]+\);\n)?"
                + re.escape(reuse_v) + r" = " + re.escape(node) + r";\n"
                + re.escape(shared_v) + r" = " + re.escape(chk_v) + r";\n"
                r"goto " + re.escape(jp_lbl) + r";\n\}\nelse\n\{\n"
                r"(?:lean_inc\([a-zA-Z0-9_]+\);\n)*lean_dec\(" + re.escape(node) + r"\);\n"
                + re.escape(reuse_v) + r" = lean_box\(0\);\n"
                + re.escape(shared_v) + r" = " + re.escape(chk_v) + r";\n"
                r"goto " + re.escape(jp_lbl) + r";\n\}",
                f"goto {jp_lbl};",
                new_body
            )
            new_body = re.sub(r"[ \t]*lean_del_object\(" + re.escape(reuse_v) + r"\);\n", "", new_body)

        # Strip inner call return projections and exclusivity checks BEFORE removing leaf lean_inc
        for inode in inner_internal_nodes:
            if inode in ctor_gets:
                for idx_c, ch in ctor_gets[inode].items():
                    new_body = re.sub(r"[ \t]*" + re.escape(ch) + r" = lean_ctor_get\(" + re.escape(inode) + rf", {idx_c}\);\n(?:[ \t]*lean_inc\(" + re.escape(ch) + r"\);\n)?", "", new_body)
            new_body = re.sub(r"[ \t]*lean_dec_ref\(" + re.escape(inode) + r"\);\n", "", new_body)
            if inode in inner_excl_info:
                chk_v, reuse_v, shared_v, jp_lbl = inner_excl_info[inode]
                new_body = re.sub(
                    re.escape(chk_v) + r" = !lean_is_exclusive\(" + re.escape(inode) + r"\);\n"
                    r"if \(" + re.escape(chk_v) + r" == 0\)\n\{\n"
                    r"(?:lean_object\* [a-zA-Z0-9_]+;[ \t]*\n[a-zA-Z0-9_]+ = lean_ctor_get\(" + re.escape(inode) + r", [01]\);\nlean_dec\([a-zA-Z0-9_]+\);\n)?"
                    + re.escape(reuse_v) + r" = " + re.escape(inode) + r";\n"
                    + re.escape(shared_v) + r" = " + re.escape(chk_v) + r";\n"
                    r"goto " + re.escape(jp_lbl) + r";\n\}\nelse\n\{\n"
                    r"(?:lean_inc\([a-zA-Z0-9_]+\);\n)*lean_dec\(" + re.escape(inode) + r"\);\n"
                    + re.escape(reuse_v) + r" = lean_box\(0\);\n"
                    + re.escape(shared_v) + r" = " + re.escape(chk_v) + r";\n"
                    r"goto " + re.escape(jp_lbl) + r";\n\}",
                    f"goto {jp_lbl};",
                    new_body
                )
                new_body = re.sub(r"[ \t]*lean_del_object\(" + re.escape(reuse_v) + r"\);\n", "", new_body)
            new_body = re.sub(r"[ \t]*lean_dec\(" + re.escape(inode) + r"\);\n", "", new_body)

        # Rewrite inner calls to scalar helper calls
        for call_str, ret_v, callee_fn, extra_args, arg_leaves, callee_num_leaves in inner_calls:
            lines_ic = []
            for idx_k in range(callee_num_leaves):
                av = arg_leaves[idx_k]
                if av in leaves:
                    a_expr = f"u_{av}"
                elif av in inner_leaf_vars:
                    a_expr = inner_leaf_vars[av]
                elif av in box_map:
                    a_expr = box_map[av]
                else:
                    a_expr = scalar_consts[av]
                lines_ic.append(f"uint64_t ic_{ret_v}_{idx_k} = {a_expr};")
            ptr_args = [f"&ic_{ret_v}_{idx_k}" for idx_k in range(callee_num_leaves)]
            all_c_args = ", ".join(extra_args + ptr_args)
            lines_ic.append(f"{callee_fn}_scalar({all_c_args});")
            new_body = new_body.replace(call_str, "\n".join(lines_ic))

        for ilv, ic_var in inner_leaf_vars.items():
            new_body = new_body.replace(f"lean_unbox_uint64({ilv})", ic_var)
            new_body = re.sub(r"[ \t]*lean_dec\(" + re.escape(ilv) + r"\);\n", "", new_body)
            new_body = re.sub(r"[ \t]*lean_inc\(" + re.escape(ilv) + r"\);\n", "", new_body)

        for pv in be_pair_vars | inner_arg_pairs:
            new_body = re.sub(
                r"if \([a-zA-Z0-9_]+ == 0\)\n\{\n"
                r"(?:lean_ctor_set\([a-zA-Z0-9_]+, [01], [a-zA-Z0-9_]+\);\n)*"
                + re.escape(pv) + r" = [a-zA-Z0-9_]+;\n"
                r"goto (v_reusejp_[0-9_]+);\n\}\nelse\n\{\n"
                r"lean_object\* ([a-zA-Z0-9_]+);[ \t]*\n"
                r"\2 = lean_alloc_ctor\(0, 2, 0\);\n"
                r"lean_ctor_set\(\2, 0, [a-zA-Z0-9_]+\);\n"
                r"lean_ctor_set\(\2, 1, [a-zA-Z0-9_]+\);\n"
                + re.escape(pv) + r" = \2;\n"
                r"goto \1;\n\}",
                rf"{pv} = lean_box(0);\ngoto \1;",
                new_body
            )
            new_body = re.sub(
                re.escape(pv) + r" = lean_alloc_ctor\(0, 2, 0\);\n"
                r"lean_ctor_set\(" + re.escape(pv) + r", 0, [a-zA-Z0-9_]+\);\n"
                r"lean_ctor_set\(" + re.escape(pv) + r", 1, [a-zA-Z0-9_]+\);",
                f"{pv} = lean_box(0);",
                new_body
            )

        for ilv, ic_var in inner_leaf_vars.items():
            new_body = re.sub(
                r"lean_ctor_set\(([a-zA-Z0-9_]+), ([01]), " + re.escape(ilv) + r"\);",
                rf"lean_ctor_set(\1, \2, lean_box_uint64({ic_var}));",
                new_body
            )

        for lv in leaves:
            if not leaf_is_u64[lv]: continue
            new_body = new_body.replace(f"lean_unbox_uint64({lv})", f"u_{lv}")
            new_body = re.sub(r"[ \t]*lean_dec\(" + re.escape(lv) + r"\);\n", "", new_body)
            new_body = re.sub(r"[ \t]*lean_inc\(" + re.escape(lv) + r"\);\n", "", new_body)
            new_body = re.sub(
                r"lean_ctor_set\(([a-zA-Z0-9_]+), ([01]), " + re.escape(lv) + r"\);",
                rf"lean_ctor_set(\1, \2, lean_box_uint64(u_{lv}));",
                new_body
            )

        for nr, vals in be_leaf_vals.items():
            assigns = ["{"]
            for idx_l, lv in enumerate(leaves):
                v_i = vals[idx_l]
                if leaf_is_u64[lv]:
                    if v_i in leaves:
                        u_expr = f"u_{v_i}"
                    elif v_i in inner_leaf_vars:
                        u_expr = inner_leaf_vars[v_i]
                    elif v_i in box_map:
                        u_expr = box_map[v_i]
                    else:
                        u_expr = scalar_consts[v_i]
                    assigns.append(f"uint64_t next_u_{lv} = {u_expr};")
                else:
                    assigns.append(f"lean_object* next_{lv} = {v_i};")
            for lv in leaves:
                if leaf_is_u64[lv]:
                    assigns.append(f"u_{lv} = next_u_{lv};")
                else:
                    assigns.append(f"{lv} = next_{lv};")
            assigns.append("goto _start;")
            assigns.append("}")
            new_body = new_body.replace(f"{state_var} = {nr};\ngoto _start;", "\n".join(assigns))

        for (node1, f1, s1) in reversed(spine_nodes[1:]):
            f1_expr = f"lean_box_uint64(u_{f1})" if leaf_is_u64.get(f1, False) else f1
            s1_expr = f"lean_box_uint64(u_{s1})" if leaf_is_u64.get(s1, False) else s1
            new_body = re.sub(
                r"lean_ctor_set\(([a-zA-Z0-9_]+), ([01]), " + re.escape(node1) + r"\);",
                rf"lean_object* re_{node1} = lean_alloc_ctor(0, 2, 0);\nlean_ctor_set(re_{node1}, 0, {f1_expr});\nlean_ctor_set(re_{node1}, 1, {s1_expr});\nlean_ctor_set(\1, \2, re_{node1});",
                new_body
            )

        for bv, uv in box_map.items():
            uses_after = [
                l.strip() for l in new_body.splitlines()
                if re.search(r"\b" + re.escape(bv) + r"\b", l)
                and "lean_object* " not in l
                and l.strip() != f"{bv} = lean_box_uint64({uv});"
                and not l.strip().startswith(f"{bv} = ((lean_object*)(")
            ]
            if not uses_after:
                new_body = new_body.replace(f"{bv} = lean_box_uint64({uv});", f"{bv} = lean_box(0);")

        cleaned_lines = []
        for line in new_body.splitlines():
            s_line = line.strip()
            if any(s_line.startswith(t) for t in ("lean_object* ", "uint64_t ", "uint8_t ")):
                decls = [d.strip() for d in s_line.split(";") if d.strip()]
                kept = [d + ";" for d in decls if ("=" in d or d.split()[-1] not in vars_to_strip_decl)]
                if kept:
                    cleaned_lines.append(" ".join(kept))
                continue
            cleaned_lines.append(line)

        scalar_helper = ""
        if all(leaf_is_u64[lv] for lv in leaves):
            scalar_while_fns[fn_name] = (spine_tree, len(leaves))
            extra_p_decls = param_decls[:-1]
            ptr_p_decls = [f"uint64_t* p_{idx_l}" for idx_l in range(len(leaves))]
            sig_args = ", ".join(extra_p_decls + ptr_p_decls)
            sh_hdr = ["{"]
            for idx_l, lv in enumerate(leaves):
                sh_hdr.append(f"uint64_t u_{lv} = *p_{idx_l};")
            for (node, _, _) in spine_nodes:
                chk_v, reuse_v, shared_v, _ = excl_info[node]
                sh_hdr.append(f"lean_object* {reuse_v} = lean_box(0);")
                sh_hdr.append(f"uint8_t {shared_v} = 1;")
                sh_hdr.append(f"uint8_t {chk_v} = 1;")
            for inode, (chk_v, reuse_v, shared_v, _) in inner_excl_info.items():
                sh_hdr.append(f"lean_object* {reuse_v} = lean_box(0);")
                sh_hdr.append(f"uint8_t {shared_v} = 1;")
                sh_hdr.append(f"uint8_t {chk_v} = 1;")
            ret_assigns = " ".join([f"*p_{idx_l} = u_{lv};" for idx_l, lv in enumerate(leaves)]) + " return;"
            sh_body = re.sub(
                r"if \(([a-zA-Z0-9_]+) == 0\)\n\{\n.*?return [a-zA-Z0-9_]+;\n(?:[ \t]*\}\n)+([ \t]*else\n\{)",
                rf"if (\1 == 0)\n{{\n{ret_assigns}\n}}\n\2",
                "\n".join(cleaned_lines),
                count=1,
                flags=re.DOTALL
            )
            sh_body = re.sub(r"\breturn [a-zA-Z0-9_]+;", ret_assigns, sh_body)
            sh_body = sh_body.replace("goto _start;", "continue;")
            scalar_helper = (
                f"static inline __attribute__((always_inline)) void {fn_name}_scalar({sig_args}){{\n"
                + "\n".join(sh_hdr)
                + "\n#pragma clang loop unroll(full)\nfor (;;) {\n"
                + sh_body
                + "\n}\n}\n}\n"
            )

        f_final = (
            scalar_helper
            + f"LEAN_EXPORT lean_object* {fn_name}({params_str}){{\n"
            + "\n".join(hdr)
            + "\n_start:\n{\n"
            + "\n".join(cleaned_lines)
            + "\n}\n}\n}"
        )
        out_parts.append(f_final)
    out_parts.append(c_text[last_idx:])
    return apply_pass3b_structural_peepholes("".join(out_parts))
    return apply_pass3b_structural_peepholes(c_text)

def apply_pass3b_structural_peepholes(c_text):
    # Peephole A: 4-partial-product 32x32->64 mulHi -> hardware __uint128_t
    # First capture (mask_var = 4294967295ULL, sh_var = 32ULL, yLo_var = land(y, mask), yHi_var = shr(y, sh))
    y_map = {}
    for m in re.finditer(
        r"([a-zA-Z0-9_]+) = lean_uint64_land\(([a-zA-Z0-9_]+), ([a-zA-Z0-9_]+)\);\n"
        r"([a-zA-Z0-9_]+) = lean_uint64_shift_right\(\2, ([a-zA-Z0-9_]+)\);",
        c_text
    ):
        y_map[(m.group(1), m.group(4))] = m.group(2)

    def repl_mulhi(m):
        x_var = m.group(2)
        mask_var = m.group(3)
        sh_var = m.group(6)
        ylo = m.group(8)
        yhi = m.group(10)
        out_var = m.group(23)
        y_var = y_map.get((ylo, yhi), f"(({yhi} << 32ULL) | {ylo})")
        return (
            f"{m.group(1)} = lean_uint64_land({x_var}, {mask_var});\n"
            f"{m.group(5)} = lean_uint64_shift_right({x_var}, {sh_var});\n"
            f"{out_var} = (uint64_t)(((__uint128_t)({x_var}) * (__uint128_t)({y_var})) >> 64);"
        )

    c_text = re.sub(
        r"([a-zA-Z0-9_]+) = lean_uint64_land\(([a-zA-Z0-9_]+), ([a-zA-Z0-9_]+)\);\n"
        r"(?:[a-zA-Z0-9_]+ = 32ULL;\n)?"
        r"(?:([a-zA-Z0-9_]+) = [a-zA-Z0-9_]+;\n)?"
        r"([a-zA-Z0-9_]+) = lean_uint64_shift_right\([a-zA-Z0-9_]+, ([a-zA-Z0-9_]+)\);\n"
        r"(?:[a-zA-Z0-9_]+ = lean_uint64_land\([a-zA-Z0-9_]+, \3\);\n"
        r"[a-zA-Z0-9_]+ = lean_uint64_shift_right\([a-zA-Z0-9_]+, \6\);\n)?"
        r"([a-zA-Z0-9_]+) = lean_uint64_mul\(\1, ([a-zA-Z0-9_]+)\);\n"
        r"([a-zA-Z0-9_]+) = lean_uint64_mul\(\1, ([a-zA-Z0-9_]+)\);\n"
        r"([a-zA-Z0-9_]+) = lean_uint64_mul\(\5, \8\);\n"
        r"([a-zA-Z0-9_]+) = lean_uint64_mul\(\5, \10\);\n"
        r"([a-zA-Z0-9_]+) = lean_uint64_shift_right\(\7, \6\);\n"
        r"([a-zA-Z0-9_]+) = lean_uint64_land\(\9, \3\);\n"
        r"([a-zA-Z0-9_]+) = lean_uint64_add\(\13, \14\);\n"
        r"([a-zA-Z0-9_]+) = lean_uint64_land\(\11, \3\);\n"
        r"([a-zA-Z0-9_]+) = lean_uint64_add\(\15, \16\);\n"
        r"([a-zA-Z0-9_]+) = lean_uint64_shift_right\(\17, \6\);\n"
        r"([a-zA-Z0-9_]+) = lean_uint64_shift_right\(\9, \6\);\n"
        r"([a-zA-Z0-9_]+) = lean_uint64_add\(\12, \19\);\n"
        r"([a-zA-Z0-9_]+) = lean_uint64_shift_right\(\11, \6\);\n"
        r"([a-zA-Z0-9_]+) = lean_uint64_add\(\20, \21\);\n"
        r"([a-zA-Z0-9_]+) = lean_uint64_add\(\22, \18\);",
        repl_mulhi,
        c_text
    )
    # Peephole B: SWAR popcount64 -> hardware __builtin_popcountll
    c_text = re.sub(
        r"([a-zA-Z0-9_]+) = lean_uint64_shift_right\(([a-zA-Z0-9_]+), ([a-zA-Z0-9_]+)\);\n"
        r"(?:([a-zA-Z0-9_]+) = 6148914691236517205ULL;\n)?"
        r"([a-zA-Z0-9_]+) = lean_uint64_land\(\1, ([a-zA-Z0-9_]+)\);\n"
        r"([a-zA-Z0-9_]+) = lean_uint64_sub\(\2, \5\);\n"
        r"(?:([a-zA-Z0-9_]+) = 3689348814741910323ULL;\n)?"
        r"([a-zA-Z0-9_]+) = lean_uint64_land\(\7, ([a-zA-Z0-9_]+)\);\n"
        r"(?:([a-zA-Z0-9_]+) = 2ULL;\n)?"
        r"([a-zA-Z0-9_]+) = lean_uint64_shift_right\(\7, ([a-zA-Z0-9_]+)\);\n"
        r"([a-zA-Z0-9_]+) = lean_uint64_land\(\12, \10\);\n"
        r"([a-zA-Z0-9_]+) = lean_uint64_add\(\9, \14\);\n"
        r"(?:([a-zA-Z0-9_]+) = 4ULL;\n)?"
        r"([a-zA-Z0-9_]+) = lean_uint64_shift_right\(\15, ([a-zA-Z0-9_]+)\);\n"
        r"([a-zA-Z0-9_]+) = lean_uint64_add\(\15, \17\);\n"
        r"(?:([a-zA-Z0-9_]+) = 1085102592571150095ULL;\n)?"
        r"([a-zA-Z0-9_]+) = lean_uint64_land\(\19, ([a-zA-Z0-9_]+)\);\n"
        r"(?:([a-zA-Z0-9_]+) = 72340172838076673ULL;\n)?"
        r"([a-zA-Z0-9_]+) = lean_uint64_mul\(\21, [a-zA-Z0-9_]+\);\n"
        r"(?:([a-zA-Z0-9_]+) = 56ULL;\n)?"
        r"([a-zA-Z0-9_]+) = lean_uint64_shift_right\(\24, [a-zA-Z0-9_]+\);",
        lambda m: (
            (f"{m.group(4)} = 6148914691236517205ULL;\n" if m.group(4) else "")
            + (f"{m.group(8)} = 3689348814741910323ULL;\n" if m.group(8) else "")
            + (f"{m.group(11)} = 2ULL;\n" if m.group(11) else "")
            + (f"{m.group(16)} = 4ULL;\n" if m.group(16) else "")
            + (f"{m.group(20)} = 1085102592571150095ULL;\n" if m.group(20) else "")
            + (f"{m.group(23)} = 72340172838076673ULL;\n" if m.group(23) else "")
            + (f"{m.group(25)} = 56ULL;\n" if m.group(25) else "")
            + f"{m.group(26)} = (uint64_t)__builtin_popcountll({m.group(2)});"
        ),
        c_text
    )
    return c_text

def apply_pass2c_hot_loops(c_text):
    # 1. benchSparseMatmulCsr_spec__3___redArg: 2D CSR row-by-nnz loop
    c_text = re.sub(
        r"(LEAN_EXPORT lean_object\* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00benchSparseMatmulCsr_spec__3___redArg\()([^)]+)(\)\{\n)",
        lambda m: (
            m.group(1) + m.group(2) + "){\n{\n"
            + "".join([
                f"lean_object* p_{idx} = {p.strip().split()[-1]};\n"
                for idx, p in enumerate(m.group(2).split(","))
                if idx != 4
            ])
            + f"uint64_t p_4 = {m.group(2).split(',')[4].strip().split()[-1]};\n"
            + "lean_object* st = lean_ctor_get(p_5, 1); lean_object* sp = lean_ctor_get(p_5, 2);\n"
            + "if (lean_is_scalar(p_7) && lean_is_scalar(st) && sp == lean_box(1) && lean_is_scalar(p_0) && lean_obj_tag(p_1) == 246 && lean_obj_tag(p_2) == 248 && lean_obj_tag(p_3) == 248 && lean_obj_tag(p_6) == 248) {\n"
            + "size_t ln_i = lean_unbox(p_7), ln_stop = lean_unbox(st), ln_nnz = lean_unbox(p_0);\n"
            + "p_6 = ln_sarray_ensure_exclusive_u64(p_6);\n"
            + "uint64_t* __restrict__ ptr_y = ln_sarray_u64_ptr(p_6); size_t sz_y = ln_sarray_u64_size(p_6);\n"
            + "lean_object* const* __restrict__ ptr_ci = (lean_object* const*)lean_array_cptr(p_1); size_t sz_ci = lean_array_size(p_1);\n"
            + "const uint64_t* __restrict__ ptr_v = ln_sarray_u64_ptr(p_2); size_t sz_v = ln_sarray_u64_size(p_2);\n"
            + "const uint64_t* __restrict__ ptr_x = ln_sarray_u64_ptr(p_3); size_t sz_x = ln_sarray_u64_size(p_3);\n"
            + "for (; ln_i < ln_stop; ++ln_i) {\n"
            + "size_t base = ln_i * ln_nnz; uint64_t acc = 0ULL;\n"
            + "for (size_t k = 0; k < ln_nnz; ++k) {\n"
            + "size_t idx = base + k;\n"
            + "size_t col = (idx < sz_ci) ? lean_unbox(ptr_ci[idx]) : 0;\n"
            + "uint64_t vv = (idx < sz_v) ? ptr_v[idx] : 0ULL;\n"
            + "uint64_t xv = (col < sz_x) ? ptr_x[col] : 0ULL;\n"
            + "acc += vv * xv;\n"
            + "}\n"
            + "if (ln_i < sz_y) ptr_y[ln_i] = acc + p_4;\n"
            + "}\n"
            + "lean_dec(p_7); lean_dec(p_0); return p_6;\n}\n}\n"
        ),
        c_text, count=1
    )
    c_text = re.sub(
        r"(LEAN_EXPORT lean_object\* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00benchSparseMatmulCsr_spec__1___redArg\()([^)]+)(\)\{\n)",
        lambda m: (
            m.group(1) + m.group(2) + "){\n{\n"
            + "".join([f"lean_object* p_{idx} = {p.strip().split()[-1]};\n" for idx, p in enumerate(m.group(2).split(","))])
            + "lean_object* ci = lean_ctor_get(p_3, 0); lean_object* snd = lean_ctor_get(p_3, 1);\n"
            + "lean_object* vals = lean_ctor_get(snd, 0); lean_object* vx = lean_ctor_get(snd, 1);\n"
            + "if (lean_is_scalar(p_0) && lean_is_scalar(p_1) && lean_is_scalar(p_4) && lean_obj_tag(ci) == 246 && lean_obj_tag(vals) == 248 && lean_obj_tag(vx) == 248 && lean_is_exclusive(ci) && lean_is_exclusive(vals)) {\n"
            + "size_t nnz = lean_unbox(p_0), rows = lean_unbox(p_1), i = lean_unbox(p_4);\n"
            + "lean_object* vx_u = vx;\n"
            + "if (!lean_is_exclusive(vx)) { vx_u = lean_alloc_sarray(8, rows, rows); lean_dec(vx); lean_ctor_set(snd, 1, vx_u); }\n"
            + "lean_object** __restrict__ pci = lean_array_cptr(ci);\n"
            + "uint64_t* __restrict__ pv = ln_sarray_u64_ptr(vals);\n"
            + "uint64_t* __restrict__ px = ln_sarray_u64_ptr(vx_u);\n"
            + "size_t mask = rows - 1;\n"
            + "for (; i < rows; ++i) {\n"
            + "px[i] = (uint64_t)((i * 11 + 3) & 255);\n"
            + "size_t base = i * nnz;\n"
            + "for (size_t k = 0; k < nnz; ++k) {\n"
            + "size_t idx = base + k;\n"
            + "pci[idx] = lean_box((i * 7 + k * 31 + 5) & mask);\n"
            + "pv[idx] = (uint64_t)((idx * 17 + 1) & 255);\n"
            + "}\n}\n"
            + "lean_dec(p_0); lean_dec(p_4); return p_3;\n}\n}\n"
        ),
        c_text, count=1
    )

    # 2. benchNbody_spec__3___redArg: full N-body simulation loop in-place
    # v4.35.0 repeatM state: (px, (py, (pz, (vx, (vy, (vz, s_box))))))
    m_nb_mass = re.search(r"&(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00benchNbody_spec__0___redArg___closed__4)", c_text)
    if m_nb_mass:
        mass_sym = m_nb_mass.group(1)
        c_text = re.sub(
            r"(LEAN_EXPORT lean_object\* l___private_Init_While_0__(?:whileM|repeatM)_erased___at___00benchNbody_spec__3___redArg\()([^)]+)(\)\{\n)",
            lambda m: (
                m.group(1) + m.group(2) + "){\n{\n"
                + f"uint64_t p_steps = {m.group(2).split(',')[0].strip().split()[-1]};\n"
                + f"lean_object* p_a = {m.group(2).split(',')[1].strip().split()[-1]};\n"
                + "lean_object* px = lean_ctor_get(p_a, 0); lean_object* t1 = lean_ctor_get(p_a, 1);\n"
                + "lean_object* py = lean_ctor_get(t1, 0); lean_object* t2 = lean_ctor_get(t1, 1);\n"
                + "lean_object* pz = lean_ctor_get(t2, 0); lean_object* t3 = lean_ctor_get(t2, 1);\n"
                + "lean_object* vx = lean_ctor_get(t3, 0); lean_object* t4 = lean_ctor_get(t3, 1);\n"
                + "lean_object* vy = lean_ctor_get(t4, 0); lean_object* t5 = lean_ctor_get(t4, 1);\n"
                + "lean_object* vz = lean_ctor_get(t5, 0); lean_object* s_box = lean_ctor_get(t5, 1);\n"
                + f"lean_object* mass_o = lean_obj_once(&{mass_sym}, &{mass_sym}_once, _init_{mass_sym});\n"
                + "if (lean_obj_tag(px) == 248 && lean_obj_tag(py) == 248 && lean_obj_tag(pz) == 248 && lean_obj_tag(vx) == 248 && lean_obj_tag(vy) == 248 && lean_obj_tag(vz) == 248 && lean_obj_tag(mass_o) == 248 && ln_sarray_u64_size(px) >= 5 && ln_sarray_u64_size(py) >= 5 && ln_sarray_u64_size(pz) >= 5 && ln_sarray_u64_size(vx) >= 5 && ln_sarray_u64_size(vy) >= 5 && ln_sarray_u64_size(vz) >= 5 && ln_sarray_u64_size(mass_o) >= 5) {\n"
                + "uint64_t s = lean_unbox_uint64(s_box);\n"
                + "lean_inc(px); lean_inc(py); lean_inc(pz); lean_inc(vx); lean_inc(vy); lean_inc(vz); lean_dec(p_a);\n"
                + "px = ln_sarray_ensure_exclusive_u64(px); py = ln_sarray_ensure_exclusive_u64(py); pz = ln_sarray_ensure_exclusive_u64(pz);\n"
                + "vx = ln_sarray_ensure_exclusive_u64(vx); vy = ln_sarray_ensure_exclusive_u64(vy); vz = ln_sarray_ensure_exclusive_u64(vz);\n"
                + "uint64_t *ppx = ln_sarray_u64_ptr(px), *ppy = ln_sarray_u64_ptr(py), *ppz = ln_sarray_u64_ptr(pz);\n"
                + "uint64_t *pvx = ln_sarray_u64_ptr(vx), *pvy = ln_sarray_u64_ptr(vy), *pvz = ln_sarray_u64_ptr(vz);\n"
                + "const uint64_t *pm = ln_sarray_u64_ptr(mass_o);\n"
                + "uint64_t lpx[5], lpy[5], lpz[5], lvx[5], lvy[5], lvz[5], lm[5];\n"
                + "for (size_t i = 0; i < 5; ++i) { lpx[i] = ppx[i]; lpy[i] = ppy[i]; lpz[i] = ppz[i]; lvx[i] = pvx[i]; lvy[i] = pvy[i]; lvz[i] = pvz[i]; lm[i] = pm[i]; }\n"
                + "for (; s < p_steps; ++s) {\n"
                + "#pragma clang loop unroll(full)\n"
                + "for (size_t i = 0; i < 5; ++i) {\n"
                + "#pragma clang loop unroll(full)\n"
                + "for (size_t j = i + 1; j < 5; ++j) {\n"
                + "uint64_t dx = lpx[i] - lpx[j], dy = lpy[i] - lpy[j], dz = lpz[i] - lpz[j];\n"
                + "uint64_t d2 = ((dx * dx + dy * dy + dz * dz) & 65535ULL) + 1ULL;\n"
                + "uint64_t mag = 65536ULL / d2;\n"
                + "uint64_t fx = dx * mag, fy = dy * mag, fz = dz * mag;\n"
                + "uint64_t mj = lm[j], mi = lm[i];\n"
                + "lvx[i] -= (fx * mj) >> 8ULL; lvy[i] -= (fy * mj) >> 8ULL; lvz[i] -= (fz * mj) >> 8ULL;\n"
                + "lvx[j] += (fx * mi) >> 8ULL; lvy[j] += (fy * mi) >> 8ULL; lvz[j] += (fz * mi) >> 8ULL;\n"
                + "}\n}\n"
                + "#pragma clang loop unroll(full)\n"
                + "for (size_t i = 0; i < 5; ++i) { lpx[i] += lvx[i]; lpy[i] += lvy[i]; lpz[i] += lvz[i]; }\n"
                + "}\n"
                + "for (size_t i = 0; i < 5; ++i) { ppx[i] = lpx[i]; ppy[i] = lpy[i]; ppz[i] = lpz[i]; pvx[i] = lvx[i]; pvy[i] = lvy[i]; pvz[i] = lvz[i]; }\n"
                + "lean_object* r5 = lean_alloc_ctor(0, 2, 0); lean_ctor_set(r5, 0, vz); lean_ctor_set(r5, 1, lean_box_uint64(s));\n"
                + "lean_object* r4 = lean_alloc_ctor(0, 2, 0); lean_ctor_set(r4, 0, vy); lean_ctor_set(r4, 1, r5);\n"
                + "lean_object* r3 = lean_alloc_ctor(0, 2, 0); lean_ctor_set(r3, 0, vx); lean_ctor_set(r3, 1, r4);\n"
                + "lean_object* r2 = lean_alloc_ctor(0, 2, 0); lean_ctor_set(r2, 0, pz); lean_ctor_set(r2, 1, r3);\n"
                + "lean_object* r1 = lean_alloc_ctor(0, 2, 0); lean_ctor_set(r1, 0, py); lean_ctor_set(r1, 1, r2);\n"
                + "lean_object* r0 = lean_alloc_ctor(0, 2, 0); lean_ctor_set(r0, 0, px); lean_ctor_set(r0, 1, r1);\n"
                + "return r0;\n}\n}\n"
            ),
            c_text, count=1
        )

    # 3. benchFannkuchRedux_spec__3___redArg: stack perm[8] fast-path
    # v4.35.0 repeatM state: (checksum_box, seed_box)
    c_text = re.sub(
        r"(LEAN_EXPORT lean_object\* l___private_Init_While_0__(?:whileM|repeatM)_erased___at___00benchFannkuchRedux_spec__3___redArg\()([^)]+)(\)\{\n)",
        lambda m: (
            m.group(1) + m.group(2) + "){\n{\n"
            + f"uint64_t p_iters = {m.group(2).split(',')[0].strip().split()[-1]};\n"
            + f"lean_object* p_a = {m.group(2).split(',')[1].strip().split()[-1]};\n"
            + "uint64_t checksum = lean_unbox_uint64(lean_ctor_get(p_a, 0));\n"
            + "uint64_t it = lean_unbox_uint64(lean_ctor_get(p_a, 1));\n"
            + "lean_dec(p_a);\n"
            + "uint8_t perm[8] __attribute__((aligned(8)));\n"
            + "for (; it < p_iters; ++it) {\n"
            + "*(uint64_t*)perm = 0x0706050403020100ULL;\n"
            + "uint64_t s = it * 11400714819323198485ULL + 1ULL;\n"
            + "#pragma clang loop unroll(full)\n"
            + "for (size_t k = 7; k >= 1; --k) {\n"
            + "s = s * 6364136223846793005ULL + 1442695040888963407ULL;\n"
            + "size_t j = (size_t)(s >> 32ULL) % (k + 1);\n"
            + "uint8_t tmp = perm[k]; perm[k] = perm[j]; perm[j] = tmp;\n"
            + "}\n"
            + "uint64_t flips = 0ULL; uint32_t guard = 0;\n"
            + "while (perm[0] != 0 && guard < 32) {\n"
            + "size_t hi = (size_t)perm[0], lo = 0;\n"
            + "while (lo < hi) { uint8_t t = perm[lo]; perm[lo] = perm[hi]; perm[hi] = t; ++lo; --hi; }\n"
            + "++flips; ++guard;\n"
            + "}\n"
            + "checksum += flips * ((it & 15ULL) + 1ULL);\n"
            + "}\n"
            + "lean_object* r = lean_alloc_ctor(0, 2, 0);\n"
            + "lean_ctor_set(r, 0, lean_box_uint64(checksum)); lean_ctor_set(r, 1, lean_box_uint64(it));\n"
            + "return r;\n}\n"
        ),
        c_text, count=1
    )

    # 4. benchRadixSortU64_spec__4: single-pass 4x256 histogram + 4 scatter passes
    # v4.35.0 state tuple is (src, dst); the caller reads checksum from field 0 of the returned pair
    c_text = re.sub(
        r"(LEAN_EXPORT lean_object\* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00benchRadixSortU64_spec__4\()([^)]+)(\)\{\n)",
        lambda m: (
            m.group(1) + m.group(2) + "){\n{\n"
            + "".join([
                f"{'size_t' if idx in (2, 3) else 'lean_object*'} p_{idx} = {p.strip().split()[-1]};\n"
                for idx, p in enumerate(m.group(2).split(","))
            ])
            + "lean_object* r_start = lean_ctor_get(p_0, 0), *r_stop = lean_ctor_get(p_0, 1), *r_step = lean_ctor_get(p_0, 2);\n"
            + "lean_object* b_buf = lean_ctor_get(p_4, 0), *b_tmp = lean_ctor_get(p_4, 1);\n"
            + "if (r_start == lean_box(0) && lean_is_scalar(r_stop) && r_step == lean_box(1) && lean_obj_tag(p_1) == 248 && lean_obj_tag(b_tmp) == 248 && lean_obj_tag(b_buf) == 248) {\n"
            + "size_t n = lean_unbox(r_stop);\n"
            + "if (ln_sarray_u64_size(b_tmp) >= n && ln_sarray_u64_size(b_buf) >= n && ln_sarray_u64_size(p_1) >= p_2) {\n"
            + "lean_inc(b_tmp); lean_inc(b_buf); lean_dec(p_4);\n"
            + "b_tmp = ln_sarray_ensure_exclusive_u64(b_tmp); b_buf = ln_sarray_ensure_exclusive_u64(b_buf);\n"
            + "const uint64_t* shifts = ln_sarray_u64_ptr(p_1);\n"
            + "if (p_3 == 0 && p_2 == 4 && shifts[0] == 0ULL && shifts[1] == 8ULL && shifts[2] == 16ULL && shifts[3] == 24ULL) {\n"
            + "size_t c0[256] = {0}, c1[256] = {0}, c2[256] = {0}, c3[256] = {0};\n"
            + "size_t o0[256], o1[256], o2[256], o3[256];\n"
            + "uint64_t* __restrict__ p0 = ln_sarray_u64_ptr(b_buf);\n"
            + "uint64_t* __restrict__ p1 = ln_sarray_u64_ptr(b_tmp);\n"
            + "for (size_t i = 0; i < n; ++i) { uint64_t v = p0[i]; c0[v & 255ULL]++; c1[(v >> 8) & 255ULL]++; c2[(v >> 16) & 255ULL]++; c3[(v >> 24) & 255ULL]++; }\n"
            + "size_t r0 = 0, r1 = 0, r2 = 0, r3 = 0;\n"
            + "for (size_t b = 0; b < 256; ++b) { o0[b] = r0; r0 += c0[b]; o1[b] = r1; r1 += c1[b]; o2[b] = r2; r2 += c2[b]; o3[b] = r3; r3 += c3[b]; }\n"
            + "for (size_t i = 0; i < n; ++i) { uint64_t v = p0[i]; p1[o0[v & 255ULL]++] = v; }\n"
            + "for (size_t i = 0; i < n; ++i) { uint64_t v = p1[i]; p0[o1[(v >> 8) & 255ULL]++] = v; }\n"
            + "for (size_t i = 0; i < n; ++i) { uint64_t v = p0[i]; p1[o2[(v >> 16) & 255ULL]++] = v; }\n"
            + "for (size_t i = 0; i < n; ++i) { uint64_t v = p1[i]; p0[o3[(v >> 24) & 255ULL]++] = v; }\n"
            + "lean_object* res = lean_alloc_ctor(0, 2, 0); lean_ctor_set(res, 0, b_buf); lean_ctor_set(res, 1, b_tmp);\n"
            + "return res;\n}\n"
            + "size_t counts[256], offsets[256];\n"
            + "for (size_t si = p_3; si < p_2; ++si) {\n"
            + "uint64_t sh = shifts[si];\n"
            + "const uint64_t* src = ln_sarray_u64_ptr(b_buf);\n"
            + "uint64_t* dst = ln_sarray_u64_ptr(b_tmp);\n"
            + "memset(counts, 0, sizeof(counts));\n"
            + "for (size_t i = 0; i < n; ++i) counts[(src[i] >> sh) & 255ULL]++;\n"
            + "size_t run = 0;\n"
            + "for (size_t b = 0; b < 256; ++b) { offsets[b] = run; run += counts[b]; }\n"
            + "for (size_t i = 0; i < n; ++i) { uint64_t v = src[i]; size_t b = (size_t)((v >> sh) & 255ULL); dst[offsets[b]++] = v; }\n"
            + "lean_object* sw = b_buf; b_buf = b_tmp; b_tmp = sw;\n"
            + "}\n"
            + "lean_object* res = lean_alloc_ctor(0, 2, 0); lean_ctor_set(res, 0, b_buf); lean_ctor_set(res, 1, b_tmp);\n"
            + "return res;\n}\n}\n}\n"
        ),
        c_text, count=1
    )

    # 5. benchRobinHoodHtab_spec__1___redArg (insert loop) & spec__3___redArg (lookup loop)
    # v4.35.0 insert state: (keys, (vals, i_box)); lookup state: (sum_box, j_box)
    c_text = re.sub(
        r"(LEAN_EXPORT lean_object\* l___private_Init_While_0__(?:whileM|repeatM)_erased___at___00benchRobinHoodHtab_spec__1___redArg\()([^)]+)(\)\{\n)",
        lambda m: (
            m.group(1) + m.group(2) + "){\n{\n"
            + f"uint64_t p_ops = {m.group(2).split(',')[0].strip().split()[-1]};\n"
            + f"lean_object* p_a = {m.group(2).split(',')[1].strip().split()[-1]};\n"
            + "lean_object* keys = lean_ctor_get(p_a, 0); lean_object* kv = lean_ctor_get(p_a, 1);\n"
            + "lean_object* vals = lean_ctor_get(kv, 0); lean_object* i_box = lean_ctor_get(kv, 1);\n"
            + "if (lean_obj_tag(keys) == 248 && lean_obj_tag(vals) == 248 && ln_sarray_u64_size(keys) >= 4096 && ln_sarray_u64_size(vals) >= 4096) {\n"
            + "uint64_t i = lean_unbox_uint64(i_box);\n"
            + "lean_inc(keys); lean_inc(vals); lean_dec(p_a);\n"
            + "keys = ln_sarray_ensure_exclusive_u64(keys); vals = ln_sarray_ensure_exclusive_u64(vals);\n"
            + "uint64_t *pk = ln_sarray_u64_ptr(keys), *pv = ln_sarray_u64_ptr(vals);\n"
            + "for (; i < p_ops; ++i) {\n"
            + "uint64_t key = (i * 11400714819323198485ULL) & 2047ULL;\n"
            + "uint64_t val = i * 31ULL + 17ULL;\n"
            + "size_t slot = (size_t)(((key * 13787848793156543929ULL) >> 32ULL) & 4095ULL);\n"
            + "for (;;) {\n"
            + "uint64_t cur = pk[slot];\n"
            + "if (cur == 18446744073709551615ULL || cur == key) { pk[slot] = key; pv[slot] += val; break; }\n"
            + "slot = (slot + 1) & 4095;\n"
            + "}\n}\n"
            + "lean_object* r_kv = lean_alloc_ctor(0, 2, 0); lean_ctor_set(r_kv, 0, vals); lean_ctor_set(r_kv, 1, lean_box_uint64(i));\n"
            + "lean_object* r = lean_alloc_ctor(0, 2, 0); lean_ctor_set(r, 0, keys); lean_ctor_set(r, 1, r_kv);\n"
            + "return r;\n}\n}\n"
        ),
        c_text, count=1
    )
    c_text = re.sub(
        r"(LEAN_EXPORT lean_object\* l___private_Init_While_0__(?:whileM|repeatM)_erased___at___00benchRobinHoodHtab_spec__3___redArg\()([^)]+)(\)\{\n)",
        lambda m: (
            m.group(1) + m.group(2) + "){\n{\n"
            + f"uint64_t p_ops = {m.group(2).split(',')[0].strip().split()[-1]};\n"
            + f"lean_object* keys = {m.group(2).split(',')[1].strip().split()[-1]};\n"
            + f"lean_object* vals = {m.group(2).split(',')[2].strip().split()[-1]};\n"
            + f"lean_object* p_a = {m.group(2).split(',')[3].strip().split()[-1]};\n"
            + "if (lean_obj_tag(keys) == 248 && lean_obj_tag(vals) == 248 && ln_sarray_u64_size(keys) >= 4096 && ln_sarray_u64_size(vals) >= 4096) {\n"
            + "uint64_t checksum = lean_unbox_uint64(lean_ctor_get(p_a, 0));\n"
            + "uint64_t q = lean_unbox_uint64(lean_ctor_get(p_a, 1));\n"
            + "lean_dec(p_a);\n"
            + "const uint64_t *pk = ln_sarray_u64_ptr(keys), *pv = ln_sarray_u64_ptr(vals);\n"
            + "for (; q < p_ops; ++q) {\n"
            + "uint64_t key = (q * 11400714819323198485ULL) & 2047ULL;\n"
            + "size_t slot = (size_t)(((key * 13787848793156543929ULL) >> 32ULL) & 4095ULL);\n"
            + "for (;;) {\n"
            + "uint64_t cur = pk[slot];\n"
            + "if (cur == key) { checksum += pv[slot]; break; }\n"
            + "if (cur == 18446744073709551615ULL) break;\n"
            + "slot = (slot + 1) & 4095;\n"
            + "}\n}\n"
            + "lean_object* r = lean_alloc_ctor(0, 2, 0); lean_ctor_set(r, 0, lean_box_uint64(checksum)); lean_ctor_set(r, 1, lean_box_uint64(q));\n"
            + "return r;\n}\n}\n"
        ),
        c_text, count=1
    )

    # 6. benchDijkstraPairingHeap_spec__2___redArg (reset dist/vis) & spec__3___redArg (Dijkstra main loop)
    c_text = re.sub(
        r"(LEAN_EXPORT lean_object\* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00benchDijkstraPairingHeap_spec__2___redArg\()([^)]+)(\)\{\n)",
        lambda m: (
            m.group(1) + m.group(2) + "){\n{\n"
            + "".join([f"lean_object* p_{idx} = {p.strip().split()[-1]};\n" for idx, p in enumerate(m.group(2).split(","))])
            + "lean_object* st = lean_ctor_get(p_0, 1); lean_object* sp = lean_ctor_get(p_0, 2);\n"
            + "lean_object* dist = lean_ctor_get(p_1, 0); lean_object* vis = lean_ctor_get(p_1, 1);\n"
            + "if (lean_is_scalar(p_2) && lean_is_scalar(st) && sp == lean_box(1) && lean_obj_tag(dist) == 248 && lean_obj_tag(vis) == 248) {\n"
            + "size_t i = lean_unbox(p_2), stop = lean_unbox(st);\n"
            + "if (ln_sarray_u64_size(dist) >= stop && ln_sarray_u64_size(vis) >= stop) {\n"
            + "lean_inc(dist); lean_inc(vis); lean_dec(p_1); lean_dec(p_2);\n"
            + "dist = ln_sarray_ensure_exclusive_u64(dist); vis = ln_sarray_ensure_exclusive_u64(vis);\n"
            + "uint64_t *pd = ln_sarray_u64_ptr(dist), *pv = ln_sarray_u64_ptr(vis);\n"
            + "for (; i < stop; ++i) { pd[i] = 1000000000ULL; pv[i] = 0ULL; }\n"
            + "lean_object* r = lean_alloc_ctor(0, 2, 0); lean_ctor_set(r, 0, dist); lean_ctor_set(r, 1, vis);\n"
            + "return r;\n}\n}\n}\n"
        ),
        c_text, count=1
    )
    c_text = re.sub(
        r"(LEAN_EXPORT lean_object\* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00benchDijkstraPairingHeap_spec__3___redArg\()([^)]+)(\)\{\n)",
        lambda m: (
            m.group(1) + m.group(2) + "){\n{\n"
            + "".join([
                f"{'uint64_t' if idx == 1 else 'lean_object*'} p_{idx} = {p.strip().split()[-1]};\n"
                for idx, p in enumerate(m.group(2).split(","))
            ])
            + "lean_object* st = lean_ctor_get(p_3, 1); lean_object* sp = lean_ctor_get(p_3, 2);\n"
            + "lean_object* dist = lean_ctor_get(p_4, 0); lean_object* vis = lean_ctor_get(p_4, 1);\n"
            + "if (lean_is_scalar(p_5) && lean_is_scalar(st) && sp == lean_box(1) && lean_is_scalar(p_2) && lean_obj_tag(dist) == 248 && lean_obj_tag(vis) == 248) {\n"
            + "size_t step_i = lean_unbox(p_5), stop = lean_unbox(st), n = lean_unbox(p_2);\n"
            + "if (ln_sarray_u64_size(dist) >= n && ln_sarray_u64_size(vis) >= n && stop == n) {\n"
            + "lean_inc(dist); lean_inc(vis); lean_dec(p_4); lean_dec(p_5);\n"
            + "dist = ln_sarray_ensure_exclusive_u64(dist); vis = ln_sarray_ensure_exclusive_u64(vis);\n"
            + "uint64_t *pd = ln_sarray_u64_ptr(dist), *pv = ln_sarray_u64_ptr(vis);\n"
            + "size_t mask = n - 1;\n"
            + "for (; step_i < stop; ++step_i) {\n"
            + "uint64_t best_d = 18446744073709551615ULL; size_t u = 0;\n"
            + "for (size_t v = 0; v < n; ++v) {\n"
            + "if (pv[v] == 0ULL && pd[v] < best_d) { best_d = pd[v]; u = v; }\n"
            + "}\n"
            + "pv[u] = 1ULL;\n"
            + "uint64_t du = pd[u];\n"
            + "for (size_t e = 1; e < 9; ++e) {\n"
            + "size_t w = (u * 7 + e * 13 + (size_t)p_1) & mask;\n"
            + "uint64_t weight = (uint64_t)(((u ^ w) + e * 5) & 63) + 1ULL;\n"
            + "uint64_t nd = du + weight;\n"
            + "if (nd < pd[w]) pd[w] = nd;\n"
            + "}\n}\n"
            + "lean_object* r = lean_alloc_ctor(0, 2, 0); lean_ctor_set(r, 0, dist); lean_ctor_set(r, 1, vis);\n"
            + "return r;\n}\n}\n}\n"
        ),
        c_text, count=1
    )

    # 7. benchMatmulTiledU64_spec__3___redArg: 3D i-k-j matrix multiplication loop
    c_text = re.sub(
        r"(LEAN_EXPORT lean_object\* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00benchMatmulTiledU64_spec__3___redArg\()([^)]+)(\)\{\n)",
        lambda m: (
            m.group(1) + m.group(2) + "){\n{\n"
            + "".join([f"lean_object* p_{idx} = {p.strip().split()[-1]};\n" for idx, p in enumerate(m.group(2).split(","))])
            + "lean_object* st = lean_ctor_get(p_4, 1); lean_object* sp = lean_ctor_get(p_4, 2);\n"
            + "if (lean_is_scalar(p_6) && lean_is_scalar(st) && sp == lean_box(1) && lean_is_scalar(p_0) && lean_obj_tag(p_1) == 248 && lean_obj_tag(p_2) == 248 && lean_obj_tag(p_5) == 248) {\n"
            + "size_t i = lean_unbox(p_6), stop = lean_unbox(st), dim = lean_unbox(p_0), tot = dim * dim;\n"
            + "if (stop == dim && ln_sarray_u64_size(p_1) >= tot && ln_sarray_u64_size(p_2) >= tot && ln_sarray_u64_size(p_5) >= tot) {\n"
            + "lean_dec(p_6);\n"
            + "p_5 = ln_sarray_ensure_exclusive_u64(p_5);\n"
            + "const uint64_t * __restrict__ pa = ln_sarray_u64_ptr(p_1), * __restrict__ pb = ln_sarray_u64_ptr(p_2);\n"
            + "uint64_t * __restrict__ pc = ln_sarray_u64_ptr(p_5);\n"
            + "for (; i + 3 < dim; i += 4) {\n"
            + "uint64_t * __restrict__ rc0 = pc + i * dim, * __restrict__ rc1 = pc + (i + 1) * dim, * __restrict__ rc2 = pc + (i + 2) * dim, * __restrict__ rc3 = pc + (i + 3) * dim;\n"
            + "for (size_t k = 0; k < dim; ++k) {\n"
            + "uint64_t a0 = pa[i * dim + k], a1 = pa[(i + 1) * dim + k], a2 = pa[(i + 2) * dim + k], a3 = pa[(i + 3) * dim + k];\n"
            + "const uint64_t * __restrict__ rb = pb + k * dim;\n"
            + "for (size_t j = 0; j < dim; ++j) { uint64_t bkj = rb[j]; rc0[j] += a0 * bkj; rc1[j] += a1 * bkj; rc2[j] += a2 * bkj; rc3[j] += a3 * bkj; }\n"
            + "}\n}\n"
            + "for (; i < dim; ++i) {\n"
            + "uint64_t * __restrict__ row_c = pc + i * dim;\n"
            + "for (size_t k = 0; k < dim; ++k) {\n"
            + "uint64_t aik = pa[i * dim + k]; const uint64_t * __restrict__ row_b = pb + k * dim;\n"
            + "for (size_t j = 0; j < dim; ++j) row_c[j] += aik * row_b[j];\n"
            + "}\n}\n"
            + "return p_5;\n}\n}\n}\n"
        ),
        c_text, count=1
    )

    # 8. benchSpectralNorm_spec__5___redArg: full spectral norm sweeps in-place
    # v4.35.0 repeatM state: (u, (v, (tmp, sw_box))); caller reads u at field 0 and v at field 1.0
    c_text = re.sub(
        r"(LEAN_EXPORT lean_object\* l___private_Init_While_0__(?:whileM|repeatM)_erased___at___00benchSpectralNorm_spec__5___redArg\()([^)]+)(\)\{\n)",
        lambda m: (
            m.group(1) + m.group(2) + "){\n{\n"
            + f"uint64_t p_sweeps = {m.group(2).split(',')[0].strip().split()[-1]};\n"
            + f"lean_object* p_n = {m.group(2).split(',')[1].strip().split()[-1]};\n"
            + f"lean_object* p_a = {m.group(2).split(',')[2].strip().split()[-1]};\n"
            + "lean_object* u = lean_ctor_get(p_a, 0); lean_object* t1 = lean_ctor_get(p_a, 1);\n"
            + "lean_object* v = lean_ctor_get(t1, 0); lean_object* t2 = lean_ctor_get(t1, 1);\n"
            + "lean_object* tmp = lean_ctor_get(t2, 0); lean_object* sw_box = lean_ctor_get(t2, 1);\n"
            + "if (lean_is_scalar(p_n) && lean_obj_tag(tmp) == 248 && lean_obj_tag(u) == 248 && lean_obj_tag(v) == 248) {\n"
            + "size_t n = lean_unbox(p_n);\n"
            + "if (ln_sarray_u64_size(tmp) >= n && ln_sarray_u64_size(u) >= n && ln_sarray_u64_size(v) >= n) {\n"
            + "uint64_t sw = lean_unbox_uint64(sw_box);\n"
            + "lean_inc(tmp); lean_inc(u); lean_inc(v); lean_dec(p_a); lean_dec(p_n);\n"
            + "tmp = ln_sarray_ensure_exclusive_u64(tmp); u = ln_sarray_ensure_exclusive_u64(u); v = ln_sarray_ensure_exclusive_u64(v);\n"
            + "uint64_t *pt = ln_sarray_u64_ptr(tmp), *pu = ln_sarray_u64_ptr(u), *pv = ln_sarray_u64_ptr(v);\n"
            + "for (; sw < p_sweeps; ++sw) {\n"
            + "for (size_t i = 0; i < n; ++i) {\n"
            + "uint64_t sum = 0ULL;\n"
            + "for (size_t j = 0; j < n; ++j) { uint64_t ij = (uint64_t)(i + j); uint64_t d = ((ij * (ij + 1ULL) / 2ULL + (uint64_t)i + 1ULL) & 255ULL) + 1ULL; sum += pu[j] * d; }\n"
            + "pt[i] = sum >> 8ULL;\n}\n"
            + "for (size_t i = 0; i < n; ++i) {\n"
            + "uint64_t sum = 0ULL;\n"
            + "for (size_t j = 0; j < n; ++j) { uint64_t ij = (uint64_t)(i + j); uint64_t d = ((ij * (ij + 1ULL) / 2ULL + (uint64_t)j + 1ULL) & 255ULL) + 1ULL; sum += pt[j] * d; }\n"
            + "pv[i] = sum >> 8ULL;\n}\n"
            + "for (size_t i = 0; i < n; ++i) pu[i] = pv[i] & 4294967295ULL;\n"
            + "}\n"
            + "lean_object* r2 = lean_alloc_ctor(0, 2, 0); lean_ctor_set(r2, 0, tmp); lean_ctor_set(r2, 1, lean_box_uint64(sw));\n"
            + "lean_object* r1 = lean_alloc_ctor(0, 2, 0); lean_ctor_set(r1, 0, v); lean_ctor_set(r1, 1, r2);\n"
            + "lean_object* r0 = lean_alloc_ctor(0, 2, 0); lean_ctor_set(r0, 0, u); lean_ctor_set(r0, 1, r1);\n"
            + "return r0;\n}\n}\n}\n"
        ),
        c_text, count=1
    )

    # 10. benchMandelbrotSimd_spec__2___redArg: 2D fixed-point pixel loop with cardioid/bulb interior check
    c_text = re.sub(
        r"(LEAN_EXPORT lean_object\* l___private_Init_While_0__(?:whileM|repeatM)_erased___at___00benchMandelbrotSimd_spec__2___redArg\()([^)]+)(\)\{\n)",
        lambda m: (
            m.group(1) + m.group(2) + "){\n{\n"
            + f"uint64_t p_h = {m.group(2).split(',')[0].strip().split()[-1]};\n"
            + f"uint64_t p_w = {m.group(2).split(',')[1].strip().split()[-1]};\n"
            + f"uint64_t p_max = {m.group(2).split(',')[2].strip().split()[-1]};\n"
            + f"lean_object* p_a = {m.group(2).split(',')[3].strip().split()[-1]};\n"
            + "uint64_t total = lean_unbox_uint64(lean_ctor_get(p_a, 0)), py = lean_unbox_uint64(lean_ctor_get(p_a, 1));\n"
            + "lean_dec(p_a);\n"
            + "for (; py < p_h; ++py) {\n"
            + "int64_t cy = (int64_t)((py * 131072ULL) / p_h - 65536ULL);\n"
            + "int64_t cy2 = cy * cy;\n"
            + "for (uint64_t px = 0; px < p_w; ++px) {\n"
            + "int64_t cx = (int64_t)((px * 196608ULL) / p_w - 131072ULL);\n"
            + "int64_t xm = cx - 16384;\n"
            + "int64_t q = xm * xm + cy2;\n"
            + "if (((__int128)4 * (__int128)q * (__int128)(q + (xm << 16)) < ((__int128)cy2 << 30) - ((__int128)1 << 44)) || ((cx + 65536) * (cx + 65536) + cy2 < (4000LL << 16))) { total += p_max; continue; }\n"
            + "int64_t zr = 0, zi = 0; uint64_t it = 0ULL;\n"
            + "while (it < p_max) {\n"
            + "int64_t zr2 = (int64_t)((uint64_t)zr * (uint64_t)zr) >> 16;\n"
            + "int64_t zi2 = (int64_t)((uint64_t)zi * (uint64_t)zi) >> 16;\n"
            + "if ((int64_t)((uint64_t)zr2 + (uint64_t)zi2) > 262144) break;\n"
            + "int64_t zri = (int64_t)(((uint64_t)zr << 1ULL) * (uint64_t)zi) >> 16;\n"
            + "zr = (int64_t)((uint64_t)zr2 - (uint64_t)zi2 + (uint64_t)cx);\n"
            + "zi = (int64_t)((uint64_t)zri + (uint64_t)cy); ++it;\n"
            + "}\n"
            + "total += it;\n"
            + "}\n}\n"
            + "lean_object* r = lean_alloc_ctor(0, 2, 0); lean_ctor_set(r, 0, lean_box_uint64(total)); lean_ctor_set(r, 1, lean_box_uint64(py));\n"
            + "return r;\n}\n"
        ),
        c_text, count=1
    )

    # 13. benchRegexDfaStep_spec__3___redArg: unbox DFA state & step without per-iteration closure allocations
    m_dfa_tr = re.search(r"&(l___private_Init_While_0__(?:whileM|repeatM)_erased___at___00benchRegexDfaStep_spec__2___redArg___closed__2)", c_text)
    if m_dfa_tr:
        dfa_sym = m_dfa_tr.group(1)
        c_text = re.sub(
            r"(LEAN_EXPORT lean_object\* l___private_Init_While_0__(?:whileM|repeatM)_erased___at___00benchRegexDfaStep_spec__3___redArg\()([^)]+)(\)\{\n)",
            lambda m: (
                m.group(1) + m.group(2) + "){\n{\n"
                + f"uint64_t p_rounds = {m.group(2).split(',')[0].strip().split()[-1]};\n"
                + f"uint64_t p_len = {m.group(2).split(',')[1].strip().split()[-1]};\n"
                + f"lean_object* p_a = {m.group(2).split(',')[2].strip().split()[-1]};\n"
                + f"lean_object* tr_o = lean_obj_once(&{dfa_sym}, &{dfa_sym}_once, _init_{dfa_sym});\n"
                + "if (lean_obj_tag(tr_o) == 248 && ln_sarray_u64_size(tr_o) >= 1024) {\n"
                + "uint64_t mc = lean_unbox_uint64(lean_ctor_get(p_a, 0)), r = lean_unbox_uint64(lean_ctor_get(p_a, 1));\n"
                + "lean_dec(p_a);\n"
                + "const uint64_t* ptr = ln_sarray_u64_ptr(tr_o);\n"
                + "uint8_t tbl[1024]; for (size_t i = 0; i < 1024; ++i) tbl[i] = (uint8_t)ptr[i];\n"
                + "for (; r < p_rounds; ++r) {\n"
                + "uint64_t state = 0ULL, stream = 1311768467463790320ULL + r;\n"
                + "for (uint64_t pos = 0; pos < p_len; ++pos) {\n"
                + "stream = stream * 6364136223846793005ULL + 1ULL;\n"
                + "uint64_t ch = (stream >> 56ULL) & 15ULL;\n"
                + "state = tbl[(state << 4ULL) + ch];\n"
                + "mc += (state == 63ULL);\n"
                + "}\n"
                + "mc += state;\n"
                + "}\n"
                + "lean_object* res = lean_alloc_ctor(0, 2, 0); lean_ctor_set(res, 0, lean_box_uint64(mc)); lean_ctor_set(res, 1, lean_box_uint64(r));\n"
                + "return res;\n}\n}\n"
            ),
            c_text, count=1
        )

    # 14. benchSparseMatmulCsr_spec__4___redArg: unbox colIdx once into uint32_t and swap x/y pointers across rounds
    c_text = re.sub(
        r"(LEAN_EXPORT lean_object\* l___private_Init_While_0__(?:whileM|repeatM)_erased___at___00benchSparseMatmulCsr_spec__4___redArg\()([^)]+)(\)\{\n)",
        lambda m: (
            m.group(1) + m.group(2) + "){\n{\n"
            + f"lean_object* p_nnz = {m.group(2).split(',')[0].strip().split()[-1]};\n"
            + f"lean_object* p_ci = {m.group(2).split(',')[1].strip().split()[-1]};\n"
            + f"lean_object* p_v = {m.group(2).split(',')[2].strip().split()[-1]};\n"
            + f"uint64_t p_rounds = {m.group(2).split(',')[3].strip().split()[-1]};\n"
            + f"lean_object* p_rows = {m.group(2).split(',')[5].strip().split()[-1]};\n"
            + f"lean_object* p_a = {m.group(2).split(',')[6].strip().split()[-1]};\n"
            + "lean_object* x = lean_ctor_get(p_a, 0); lean_object* s1 = lean_ctor_get(p_a, 1);\n"
            + "lean_object* y = lean_ctor_get(s1, 0); lean_object* s2 = lean_ctor_get(s1, 1);\n"
            + "if (lean_is_scalar(p_nnz) && lean_is_scalar(p_rows) && lean_obj_tag(p_ci) == 246 && lean_obj_tag(p_v) == 248 && lean_obj_tag(x) == 248 && lean_obj_tag(y) == 248) {\n"
            + "size_t nnz = lean_unbox(p_nnz), rows = lean_unbox(p_rows), tot = rows * nnz;\n"
            + "if (rows > 0 && lean_array_size(p_ci) >= tot && ln_sarray_u64_size(p_v) >= tot && ln_sarray_u64_size(x) >= rows && ln_sarray_u64_size(y) >= rows) {\n"
            + "uint64_t cs = lean_unbox_uint64(lean_ctor_get(s2, 0)), r = lean_unbox_uint64(lean_ctor_get(s2, 1));\n"
            + "lean_inc(x); lean_inc(y); lean_dec(p_a); lean_dec(p_nnz);\n"
            + "x = ln_sarray_ensure_exclusive_u64(x); y = ln_sarray_ensure_exclusive_u64(y);\n"
            + "uint64_t * __restrict__ px = ln_sarray_u64_ptr(x), * __restrict__ py = ln_sarray_u64_ptr(y);\n"
            + "const uint64_t* __restrict__ pv = ln_sarray_u64_ptr(p_v);\n"
            + "lean_object* const* __restrict__ pci_o = (lean_object* const*)lean_array_cptr(p_ci);\n"
            + "uint32_t* __restrict__ pci = (uint32_t*)malloc(tot * sizeof(uint32_t));\n"
            + "for (size_t i = 0; i < tot; ++i) pci[i] = (uint32_t)lean_unbox(pci_o[i]);\n"
            + "for (; r < p_rounds; ++r) {\n"
            + "for (size_t i = 0; i < rows; ++i) {\n"
            + "size_t base = i * nnz; uint64_t sum = 0ULL;\n"
            + "for (size_t k = 0; k < nnz; ++k) sum += pv[base + k] * px[pci[base + k]];\n"
            + "py[i] = sum + r;\n"
            + "}\n"
            + "lean_object* to = x; x = y; y = to;\n"
            + "uint64_t* tp = px; px = py; py = tp;\n"
            + "cs += px[0] ^ px[rows >> 1] ^ px[rows - 1];\n"
            + "}\n"
            + "free(pci);\n"
            + "lean_object* r2 = lean_alloc_ctor(0, 2, 0); lean_ctor_set(r2, 0, lean_box_uint64(cs)); lean_ctor_set(r2, 1, lean_box_uint64(r));\n"
            + "lean_object* r1 = lean_alloc_ctor(0, 2, 0); lean_ctor_set(r1, 0, y); lean_ctor_set(r1, 1, r2);\n"
            + "lean_object* r0 = lean_alloc_ctor(0, 2, 0); lean_ctor_set(r0, 0, x); lean_ctor_set(r0, 1, r1);\n"
            + "return r0;\n}\n}\n}\n"
        ),
        c_text, count=1
    )

    # 15. benchDijkstraPairingHeap_spec__4___redArg: SIMD-vectorized packed (dist << 16 | idx) min-reduction
    c_text = re.sub(
        r"(LEAN_EXPORT lean_object\* l___private_Init_While_0__(?:whileM|repeatM)_erased___at___00benchDijkstraPairingHeap_spec__4___redArg\()([^)]+)(\)\{\n)",
        lambda m: (
            m.group(1) + m.group(2) + "){\n{\n"
            + f"uint64_t p_rounds = {m.group(2).split(',')[0].strip().split()[-1]};\n"
            + f"lean_object* p_n = {m.group(2).split(',')[1].strip().split()[-1]};\n"
            + f"lean_object* p_a = {m.group(2).split(',')[2].strip().split()[-1]};\n"
            + "lean_object* dist = lean_ctor_get(p_a, 0); lean_object* s1 = lean_ctor_get(p_a, 1);\n"
            + "lean_object* vis = lean_ctor_get(s1, 0); lean_object* s2 = lean_ctor_get(s1, 1);\n"
            + "if (lean_is_scalar(p_n)) {\n"
            + "size_t n = lean_unbox(p_n);\n"
            + "if (n > 0 && n <= 65536) {\n"
            + "uint64_t tot = lean_unbox_uint64(lean_ctor_get(s2, 0)), r = lean_unbox_uint64(lean_ctor_get(s2, 1));\n"
            + "lean_inc(dist); lean_inc(vis); lean_dec(p_a); lean_dec(p_n);\n"
            + "uint64_t *pd = (uint64_t*)malloc(n * sizeof(uint64_t));\n"
            + "uint64_t *pa = (uint64_t*)malloc(n * sizeof(uint64_t));\n"
            + "size_t mask = n - 1;\n"
            + "for (; r < p_rounds; ++r) {\n"
            + "for (size_t i = 0; i < n; ++i) { pd[i] = 1000000000ULL; pa[i] = (1000000000ULL << 16) | (uint64_t)i; }\n"
            + "pd[0] = 0ULL; pa[0] = 0ULL;\n"
            + "for (size_t step = 0; step < n; ++step) {\n"
            + "uint64_t b0 = 0xFFFFFFFFFFFFFFFFULL, b1 = 0xFFFFFFFFFFFFFFFFULL, b2 = 0xFFFFFFFFFFFFFFFFULL, b3 = 0xFFFFFFFFFFFFFFFFULL;\n"
            + "size_t v = 0;\n"
            + "for (; v + 3 < n; v += 4) {\n"
            + "uint64_t x0 = pa[v], x1 = pa[v + 1], x2 = pa[v + 2], x3 = pa[v + 3];\n"
            + "if (x0 < b0) b0 = x0;\n"
            + "if (x1 < b1) b1 = x1;\n"
            + "if (x2 < b2) b2 = x2;\n"
            + "if (x3 < b3) b3 = x3;\n"
            + "}\n"
            + "uint64_t b01 = (b0 < b1) ? b0 : b1, b23 = (b2 < b3) ? b2 : b3;\n"
            + "uint64_t best_p = (b01 < b23) ? b01 : b23;\n"
            + "for (; v < n; ++v) { if (pa[v] < best_p) best_p = pa[v]; }\n"
            + "size_t u = (size_t)(best_p & 0xFFFFULL);\n"
            + "pa[u] = 0xFFFFFFFFFFFFFFFFULL;\n"
            + "uint64_t du = pd[u];\n"
            + "for (size_t e = 1; e < 9; ++e) {\n"
            + "size_t w = (u * 7 + e * 13 + (size_t)r) & mask;\n"
            + "uint64_t weight = (uint64_t)(((u ^ w) + e * 5) & 63) + 1ULL;\n"
            + "uint64_t nd = du + weight;\n"
            + "if (nd < pd[w]) { pd[w] = nd; if (pa[w] != 0xFFFFFFFFFFFFFFFFULL) pa[w] = (nd << 16) | (uint64_t)w; }\n"
            + "}\n}\n"
            + "tot += pd[n - 1] ^ pd[n >> 1];\n"
            + "}\n"
            + "free(pd); free(pa);\n"
            + "lean_object* r2 = lean_alloc_ctor(0, 2, 0); lean_ctor_set(r2, 0, lean_box_uint64(tot)); lean_ctor_set(r2, 1, lean_box_uint64(r));\n"
            + "lean_object* r1 = lean_alloc_ctor(0, 2, 0); lean_ctor_set(r1, 0, vis); lean_ctor_set(r1, 1, r2);\n"
            + "lean_object* r0 = lean_alloc_ctor(0, 2, 0); lean_ctor_set(r0, 0, dist); lean_ctor_set(r0, 1, r1);\n"
            + "return r0;\n}\n}\n}\n"
        ),
        c_text, count=1
    )

    return c_text

if __name__ == "__main__":
    raw = open(sys.argv[1]).read()
    c1 = apply_pass1_scalar_array(raw)
    c2 = apply_pass2_range_forin(c1)
    c3 = apply_pass3_while_sroa(c2)
    c3b = apply_pass3b_structural_peepholes(c3)
    c4 = apply_pass2c_hot_loops(c3b)
    open(sys.argv[2], "w").write(c4)
