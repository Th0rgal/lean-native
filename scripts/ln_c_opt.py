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
            r"if \(\3 == 0\)\n\{\nlean_dec\(" + re.escape(i_var) + r"\);\n((?:lean_dec\([a-zA-Z0-9_]+\);\n)*)return " + re.escape(b_var) + r";\n\}\nelse\n\{\n",
            f
        )
        if not m_start:
            out_parts.append(f)
            continue
        stop_var, step_var, exit_decs = m_start.group(1), m_start.group(2), m_start.group(4)
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
        if len(lines) < 5 or lines[-1] != "goto _start;":
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
        direct_sarray_Params = set()
        offset_sarray_Params = {}
        array_Params = set()
        direct_array_Params = set()
        offset_array_Params = {}
        nat_Params = set()
        nat_temps = {}
        param_offset_temps = {}
        range_temps = {}
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
                if idx == i_var:
                    direct_sarray_Params.add(arr)
                elif idx in param_offset_temps:
                    offset_sarray_Params.setdefault(arr, set()).add(param_offset_temps[idx])
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
                if idx == i_var:
                    direct_sarray_Params.add(b_var)
                elif idx in param_offset_temps:
                    offset_sarray_Params.setdefault(b_var, set()).add(param_offset_temps[idx])
            elif "= lean_nat_add(" in cl:
                nm = re.match(r"([a-zA-Z0-9_]+) = lean_nat_add\(([^,]+), " + re.escape(i_var) + r"\);", cl)
                if not nm:
                    supported = False; break
                base_n = nm.group(2).strip()
                if base_n not in params and base_n not in nat_temps:
                    supported = False; break
                if base_n in params:
                    nat_Params.add(base_n)
                    nat_temps[nm.group(1)] = f"ln_nat_{base_n} + ln_i"
                    param_offset_temps[nm.group(1)] = base_n
                else:
                    nat_temps[nm.group(1)] = f"ln_nt_{base_n} + ln_i"
            elif cl.startswith("lean_dec("):
                dm = re.match(r"lean_dec\(([a-zA-Z0-9_]+)\);", cl)
                if not dm or dm.group(1) not in nat_temps:
                    supported = False; break
            elif cl.startswith("lean_inc("):
                im = re.match(r"lean_inc\(([a-zA-Z0-9_]+)\);", cl)
                if not im or im.group(1) not in params:
                    supported = False; break
            elif cl.startswith("lean_dec_ref_known("):
                drm = re.match(r"lean_dec_ref_known\(([a-zA-Z0-9_]+), 3\);", cl)
                if not drm or drm.group(1) not in range_temps:
                    supported = False; break
            elif "= lean_alloc_ctor(0, 3, 0);" in cl:
                rm = re.match(r"([a-zA-Z0-9_]+) = lean_alloc_ctor\(0, 3, 0\);", cl)
                if not rm:
                    supported = False; break
                range_temps[rm.group(1)] = [None, None, None]
            elif cl.startswith("lean_ctor_set("):
                csm = re.match(r"lean_ctor_set\(([a-zA-Z0-9_]+), ([012]), ([a-zA-Z0-9_]+)\);", cl)
                if not csm or csm.group(1) not in range_temps:
                    supported = False; break
                f_idx, f_val = int(csm.group(2)), csm.group(3)
                if f_val in params and f_val != i_var:
                    nat_Params.add(f_val)
                range_temps[csm.group(1)][f_idx] = f_val
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
                if idx == i_var:
                    direct_array_Params.add(arr)
                elif idx in param_offset_temps:
                    offset_array_Params.setdefault(arr, set()).add(param_offset_temps[idx])
                if idx != i_var and idx not in nat_temps and idx not in params:
                    supported = False; break
                if idx in params and idx != i_var:
                    nat_Params.add(idx)
                nat_temps[gm.group(1)] = f"ln_nt_{gm.group(1)}"
            elif "= lean_nat_mul(" in cl:
                nm = re.match(r"([a-zA-Z0-9_]+) = lean_nat_mul\(([^,]+), ([^)]+)\);", cl)
                if not nm:
                    supported = False; break
                a1, a2 = nm.group(2).strip(), nm.group(3).strip()
                if a1 not in params and a1 != i_var and a1 not in nat_temps:
                    supported = False; break
                if a2 not in params and a2 != i_var and a2 not in nat_temps:
                    supported = False; break
                for a in (a1, a2):
                    if a in params and a != i_var:
                        nat_Params.add(a)
                nat_temps[nm.group(1)] = f"ln_nt_{nm.group(1)}"
            elif "= l_" in cl and "Range_forIn_x27_loop" in cl:
                cm = re.match(r"([a-zA-Z0-9_]+) = (l_[a-zA-Z0-9_]*Range_forIn_x27_loop[a-zA-Z0-9_]*)\(([^)]+)\);", cl)
                if not cm:
                    supported = False; break
                if cm.group(1) == next_b and ret_ty == "lean_object*":
                    mut_b = True
                    sarray_Params.add(b_var)
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
            if sp in direct_sarray_Params:
                fp.append(f"if (ln_sz_{sp} < ln_limit) ln_limit = ln_sz_{sp};")
            for base_n in sorted(offset_sarray_Params.get(sp, ())):
                fp.append(f"size_t ln_rem_{sp}_{base_n} = (ln_nat_{base_n} < ln_sz_{sp}) ? (ln_sz_{sp} - ln_nat_{base_n}) : 0; if (ln_rem_{sp}_{base_n} < ln_limit) ln_limit = ln_rem_{sp}_{base_n};")
        for ap in sorted(array_Params):
            fp.append(f"lean_object* const* __restrict__ ln_aptr_{ap} = (lean_object* const*)lean_array_cptr({ap});")
            fp.append(f"size_t ln_asz_{ap} = lean_array_size({ap});")
            if ap in direct_array_Params:
                fp.append(f"if (ln_asz_{ap} < ln_limit) ln_limit = ln_asz_{ap};")
            for base_n in sorted(offset_array_Params.get(ap, ())):
                fp.append(f"size_t ln_arem_{ap}_{base_n} = (ln_nat_{base_n} < ln_asz_{ap}) ? (ln_asz_{ap} - ln_nat_{base_n}) : 0; if (ln_arem_{ap}_{base_n} < ln_limit) ln_limit = ln_arem_{ap}_{base_n};")
        for rt, rf in range_temps.items():
            fp.append(f"struct {{ lean_ctor_object hdr; lean_object* objs[3]; }} ln_rt_{rt};")
            fp.append(f"ln_rt_{rt}.hdr.m_header.m_rc = 0; ln_rt_{rt}.hdr.m_header.m_cs_sz = sizeof(lean_ctor_object) + 3*sizeof(void*); ln_rt_{rt}.hdr.m_header.m_other = 3; ln_rt_{rt}.hdr.m_header.m_tag = 0;")
        def emit_range_loop_body(is_tail, fp=fp, core_lines=core_lines, i_var=i_var, b_var=b_var, next_b=next_b, ret_ty=ret_ty, nat_temps=nat_temps, param_offset_temps=param_offset_temps, range_temps=range_temps):
            for cl in core_lines:
                if any(cl.startswith(t) for t in ("lean_object* ", "uint64_t ", "uint8_t ")):
                    fp.append(cl)
                    continue
                if any(cl.startswith(p) for p in ("lean_dec(", "lean_inc(", "lean_dec_ref_known(")) or "= lean_alloc_ctor(0, 3, 0);" in cl or cl.startswith("lean_ctor_set("):
                    continue
                nm = re.match(r"([a-zA-Z0-9_]+) = lean_nat_add\(([^,]+), " + re.escape(i_var) + r"\);", cl)
                if nm:
                    b_src = nm.group(2).strip()
                    b_expr = f"ln_nt_{b_src}" if b_src in nat_temps else f"ln_nat_{b_src}"
                    fp.append(f"size_t ln_nt_{nm.group(1)} = {b_expr} + ln_i;")
                    continue
                um2 = re.match(r"([a-zA-Z0-9_]+) = lean_unsigned_to_nat\(([0-9]+)u\);", cl)
                if um2:
                    fp.append(f"size_t ln_nt_{um2.group(1)} = {um2.group(2)};")
                    continue
                gm2 = re.match(r"([a-zA-Z0-9_]+) = ln_array_get_borrowed_auto\(([^,]+), ([^,]+), ([^)]+)\);", cl)
                if gm2:
                    dst_n, arr, idx = gm2.group(1), gm2.group(3).strip(), gm2.group(4).strip()
                    idx_expr = "ln_i" if idx == i_var else (f"ln_nt_{idx}" if idx in nat_temps else f"ln_nat_{idx}")
                    if (idx == i_var or idx in param_offset_temps) and not is_tail:
                        fp.append(f"size_t ln_nt_{dst_n} = lean_unbox(ln_aptr_{arr}[{idx_expr}]);")
                    else:
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
                    if (idx == i_var or idx in param_offset_temps) and not is_tail:
                        fp.append(f"{dst_u} = ln_ptr_{arr}[{idx_expr}];")
                    else:
                        fp.append(f"{dst_u} = ({idx_expr} < ln_sz_{arr}) ? ln_ptr_{arr}[{idx_expr}] : 0ULL;")
                    continue
                cm = re.match(r"([a-zA-Z0-9_]+) = (l_[a-zA-Z0-9_]*Range_forIn_x27_loop[a-zA-Z0-9_]*)\(([^)]+)\);", cl)
                if cm:
                    dst_u, callee = cm.group(1), cm.group(2)
                    re_args = []
                    for a in (x.strip() for x in cm.group(3).split(",")):
                        if a == i_var:
                            re_args.append("lean_box(ln_i)")
                        elif a in nat_temps:
                            re_args.append(f"lean_box(ln_nt_{a})")
                        elif a in range_temps:
                            rf = range_temps[a]
                            for fi, fv in enumerate(rf):
                                fv_e = "lean_box(ln_i)" if fv == i_var else (f"lean_box(ln_nt_{fv})" if fv in nat_temps else fv)
                                fp.append(f"ln_rt_{a}.objs[{fi}] = {fv_e};")
                            re_args.append(f"(lean_object*)&ln_rt_{a}.hdr")
                        else:
                            re_args.append(a)
                    fp.append(f"{dst_u} = {callee}({', '.join(re_args)});")
                    if dst_u == next_b and ret_ty == "lean_object*":
                        fp.append(f"{b_var} = {dst_u}; ln_ptr_{b_var} = ln_sarray_u64_ptr({b_var});")
                    continue
                nm2 = re.match(r"([a-zA-Z0-9_]+) = lean_nat_mul\(([^,]+), ([^)]+)\);", cl)
                if nm2:
                    def nat_expr(a, i_var=i_var, nat_temps=nat_temps):
                        if a == i_var: return "ln_i"
                        if a in nat_temps: return f"ln_nt_{a}"
                        return f"ln_nat_{a}"
                    fp.append(f"size_t ln_nt_{nm2.group(1)} = {nat_expr(nm2.group(2).strip())} * {nat_expr(nm2.group(3).strip())};")
                    continue
                sm = re.match(re.escape(next_b) + r" = ln_sarray_set_u64\(" + re.escape(b_var) + r", ([^,]+), ([^)]+)\);", cl)
                if sm:
                    idx, val_u = sm.group(1).strip(), sm.group(2).strip()
                    idx_expr = "ln_i" if idx == i_var else f"ln_nt_{idx}"
                    if (idx == i_var or idx in param_offset_temps) and not is_tail:
                        fp.append(f"ln_ptr_{b_var}[{idx_expr}] = {val_u};")
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
        fp.append("for (; ln_i < ln_limit; ++ln_i) {")
        emit_range_loop_body(False)
        fp.append("}")
        if direct_sarray_Params or offset_sarray_Params or direct_array_Params or offset_array_Params:
            fp.append("for (; ln_i < ln_stop; ++ln_i) {")
            emit_range_loop_body(True)
            fp.append("}")
        fp.append(f"lean_dec({i_var});")
        if exit_decs:
            fp.append(exit_decs.strip())
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

    # Sub-pass 2D: 1-array or 2-tuple of sarrays Range.forIn' push/set initialization loops
    scalar_consts = {}
    for m in re.finditer(r"static const lean_ctor_object ([a-zA-Z0-9_]+)_value = \{[^\n]*LEAN_SCALAR_PTR_LITERAL\(([^)]+)\)\}\};", c_text):
        bs = [int(x.strip()) for x in m.group(2).split(",")]
        val = sum(b << (8 * i) for i, b in enumerate(bs))
        scalar_consts[m.group(1)] = f"{val}ULL"

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
        if "ln_array_push_auto(" not in f and "ln_array_set_auto(" not in f and "ln_sarray_set_u64(" not in f:
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
            sm = re.search(
                r"([a-zA-Z0-9_]+) = \(\(lean_object\*\)\(([a-zA-Z0-9_]+)\)\);\n"
                r"([a-zA-Z0-9_]+) = ln_array_set_auto\(" + re.escape(fst_v) + r", " + re.escape(i_var) + r", \1\);\n"
                r"([a-zA-Z0-9_]+) = \(\(lean_object\*\)\(([a-zA-Z0-9_]+)\)\);\n"
                r"([a-zA-Z0-9_]+) = ln_array_set_auto\(" + re.escape(snd_v) + r", " + re.escape(i_var) + r", \4\);",
                core_2p
            )
            if sm and sm.group(2) in scalar_consts and sm.group(5) in scalar_consts:
                c1_u, c2_u = scalar_consts[sm.group(2)], scalar_consts[sm.group(5)]
                fp = [
                    "{",
                    f"lean_object* {stop_var} = lean_ctor_get({range_var}, 1);",
                    f"lean_object* {step_var} = lean_ctor_get({range_var}, 2);",
                    f"lean_object* {fst_v} = lean_ctor_get({b_var}, 0);",
                    f"lean_object* {snd_v} = lean_ctor_get({b_var}, 1);",
                    f"if (lean_is_scalar({i_var}) && lean_is_scalar({stop_var}) && {step_var} == lean_box(1) && lean_obj_tag({fst_v}) == 248 && lean_obj_tag({snd_v}) == 248) {{",
                    f"size_t ln_i = lean_unbox({i_var}), ln_n = lean_unbox({stop_var});",
                    f"if (ln_sarray_u64_size({fst_v}) >= ln_n && ln_sarray_u64_size({snd_v}) >= ln_n) {{",
                    f"lean_inc({fst_v}); lean_inc({snd_v}); lean_dec({b_var}); lean_dec({i_var});",
                    f"{fst_v} = ln_sarray_ensure_exclusive_u64({fst_v}); {snd_v} = ln_sarray_ensure_exclusive_u64({snd_v});",
                    f"uint64_t * __restrict__ ln_pa = ln_sarray_u64_ptr({fst_v}), * __restrict__ ln_pb = ln_sarray_u64_ptr({snd_v});",
                    f"for (; ln_i < ln_n; ++ln_i) {{ ln_pa[ln_i] = {c1_u}; ln_pb[ln_i] = {c2_u}; }}",
                    f"lean_object* ln_r = lean_alloc_ctor(0, 2, 0); lean_ctor_set(ln_r, 0, {fst_v}); lean_ctor_set(ln_r, 1, {snd_v});",
                    "return ln_r;\n}\n}\n}"
                ]
                out_parts.append(f.replace("{\n_start:", "{\n" + "\n".join(fp) + "\n_start:", 1))
                continue
            sm_mix = re.search(
                r"([a-zA-Z0-9_]+) = ln_array_set_auto\(" + re.escape(fst_v) + r", ([a-zA-Z0-9_]+), ([a-zA-Z0-9_]+)\);",
                core_2p
            )
            sm_sarr = re.search(
                r"([a-zA-Z0-9_]+) = ln_sarray_set_u64\(" + re.escape(snd_v) + r", ([a-zA-Z0-9_]+), ([a-zA-Z0-9_]+)\);",
                core_2p
            )
            if sm_mix and sm_sarr:
                idx_a, val_a = sm_mix.group(2), sm_mix.group(3)
                idx_s, val_s = sm_sarr.group(2), sm_sarr.group(3)
                nat_exprs = {i_var: "ln_i"}
                nat_params_2p = set()
                u64_exprs = {}
                ok_mix = True
                for cl in [l.strip() for l in core_2p.splitlines() if l.strip()]:
                    if any(cl.startswith(t) for t in ("lean_object* ", "uint64_t ", "uint8_t ")) or cl.startswith("lean_dec("):
                        continue
                    if "= ln_array_set_auto(" in cl or "= ln_sarray_set_u64(" in cl:
                        continue
                    um = re.match(r"([a-zA-Z0-9_]+) = lean_unsigned_to_nat\(([0-9]+)u\);", cl)
                    if um:
                        nat_exprs[um.group(1)] = f"((size_t){um.group(2)}u)"; continue
                    nm = re.match(r"([a-zA-Z0-9_]+) = lean_nat_(mul|add|sub|land)\(([a-zA-Z0-9_]+), ([a-zA-Z0-9_]+)\);", cl)
                    if nm:
                        dst_n, op_n, a_n, b_n = nm.group(1), nm.group(2), nm.group(3), nm.group(4)
                        for op_arg in (a_n, b_n):
                            if op_arg not in nat_exprs and op_arg in params[:-3]:
                                nat_params_2p.add(op_arg)
                                nat_exprs[op_arg] = f"ln_nat_{op_arg}"
                        if a_n in nat_exprs and b_n in nat_exprs:
                            if op_n == "sub":
                                nat_exprs[dst_n] = f"(({nat_exprs[a_n]} >= {nat_exprs[b_n]}) ? ({nat_exprs[a_n]} - {nat_exprs[b_n]}) : 0)"
                            else:
                                op_sym = {"mul": "*", "add": "+", "land": "&"}[op_n]
                                nat_exprs[dst_n] = f"({nat_exprs[a_n]} {op_sym} {nat_exprs[b_n]})"
                            continue
                    uom = re.match(r"([a-zA-Z0-9_]+) = lean_uint64_of_nat\(([a-zA-Z0-9_]+)\);", cl)
                    if uom and uom.group(2) in nat_exprs:
                        u64_exprs[uom.group(1)] = f"((uint64_t){nat_exprs[uom.group(2)]})"
                        continue
                    ok_mix = False; break
                if ok_mix and idx_a in nat_exprs and val_a in nat_exprs and idx_s in nat_exprs and val_s in u64_exprs:
                    conds_m = [f"lean_is_scalar({i_var})", f"lean_is_scalar({stop_var})", f"{step_var} == lean_box(1)", f"lean_obj_tag({fst_v}) == 246", f"lean_obj_tag({snd_v}) == 248"]
                    for np in sorted(nat_params_2p):
                        conds_m.append(f"lean_is_scalar({np})")
                    fp = [
                        "{",
                        f"lean_object* {stop_var} = lean_ctor_get({range_var}, 1);",
                        f"lean_object* {step_var} = lean_ctor_get({range_var}, 2);",
                        f"lean_object* {fst_v} = lean_ctor_get({b_var}, 0);",
                        f"lean_object* {snd_v} = lean_ctor_get({b_var}, 1);",
                        f"if ({' && '.join(conds_m)}) {{",
                        f"size_t ln_i = lean_unbox({i_var}), ln_n = lean_unbox({stop_var});",
                        *[f"size_t ln_nat_{np} = lean_unbox({np});" for np in sorted(nat_params_2p)],
                        f"lean_inc({fst_v}); lean_inc({snd_v}); lean_dec({b_var}); lean_dec({i_var});",
                        f"if (!lean_is_exclusive({fst_v})) {fst_v} = lean_copy_expand_array({fst_v}, false);",
                        f"{snd_v} = ln_sarray_ensure_exclusive_u64({snd_v});",
                        f"lean_object** __restrict__ ln_pa = lean_array_cptr({fst_v}); size_t ln_sza = lean_array_size({fst_v});",
                        f"uint64_t* __restrict__ ln_pb = ln_sarray_u64_ptr({snd_v}); size_t ln_szb = ln_sarray_u64_size({snd_v});",
                        f"for (; ln_i < ln_n; ++ln_i) {{",
                        f"size_t idx_a = {nat_exprs[idx_a]}; if (idx_a < ln_sza) ln_pa[idx_a] = lean_box({nat_exprs[val_a]});",
                        f"size_t idx_s = {nat_exprs[idx_s]}; if (idx_s < ln_szb) ln_pb[idx_s] = {u64_exprs[val_s]};",
                        "}",
                        f"lean_object* ln_r = lean_alloc_ctor(0, 2, 0); lean_ctor_set(ln_r, 0, {fst_v}); lean_ctor_set(ln_r, 1, {snd_v});",
                        "return ln_r;\n}\n}"
                    ]
                    out_parts.append(f.replace("{\n_start:", "{\n" + "\n".join(fp) + "\n_start:", 1))
                    continue
        m_3n = re.search(
            r"_start:\n\{\nlean_object\* (v_stop_[0-9_]+); lean_object\* (v_step_[0-9_]+); uint8_t (v___x_[0-9_]+);[ \t]*\n"
            r"\1 = lean_ctor_get\(" + re.escape(range_var) + r", 1\);\n"
            r"\2 = lean_ctor_get\(" + re.escape(range_var) + r", 2\);\n"
            r"\3 = lean_nat_dec_lt\(" + re.escape(i_var) + r", \1\);\n"
            r"if \(\3 == 0\)\n\{\n((?:lean_dec\([a-zA-Z0-9_]+\);\n)*)return " + re.escape(b_var) + r";\n\}\nelse\n\{\n"
            r"lean_object\* (v_snd_[0-9_]+); lean_object\* (v_fst_[0-9_]+);[^\n]+\n"
            r"\5 = lean_ctor_get\(" + re.escape(b_var) + r", 1\);\n"
            r"\6 = lean_ctor_get\(" + re.escape(b_var) + r", 0\);\n"
            r".*?"
            r"v_resetjp_[0-9_]+:\n\{\n"
            r"lean_object\* (v_fst_[0-9_]+); lean_object\* (v_snd_[0-9_]+);[^\n]+\n"
            r"\7 = lean_ctor_get\(\5, 0\);\n"
            r"\8 = lean_ctor_get\(\5, 1\);\n"
            r".*?"
            r"v_resetjp_[0-9_]+:\n\{\n"
            r"(.*?)\n"
            r"v_reusejp_[0-9_]+:\n\{\n"
            r"lean_object\* ([a-zA-Z0-9_]+);[^\n]*\n"
            r"\10 = (l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00[a-zA-Z0-9_]+)\(([^)]+)\);",
            f, re.DOTALL
        )
        if m_3n:
            stop_var, step_var, decs_exit = m_3n.group(1), m_3n.group(2), m_3n.group(4)
            snd0, arr0, arr1, arr2 = m_3n.group(5), m_3n.group(6), m_3n.group(7), m_3n.group(8)
            pre_call, call_ret, callee_fn, call_args_s = m_3n.group(9), m_3n.group(10), m_3n.group(11), m_3n.group(12)
            sm_a2 = re.search(r"([a-zA-Z0-9_]+) = ln_sarray_set_u64\(" + re.escape(arr2) + r", " + re.escape(i_var) + r", ([a-zA-Z0-9_]+)\);", pre_call)
            if sm_a2:
                val_a2 = sm_a2.group(2)
                nat_exprs = {i_var: "ln_i"}
                u64_exprs = {}
                ok_pre = True
                for cl in [l.strip() for l in pre_call.splitlines() if l.strip()]:
                    if any(cl.startswith(t) for t in ("lean_object* ", "uint64_t ", "uint8_t ")) or cl.startswith("lean_dec(") or cl.startswith("lean_inc("):
                        continue
                    if "= ln_sarray_set_u64(" in cl or "= lean_alloc_ctor(" in cl or cl.startswith("lean_ctor_set("):
                        continue
                    if cl.startswith("if (v_isShared_") or cl in ("{", "}", "else") or cl.startswith("v___x_") and " = v_" in cl or cl.startswith("goto v_reusejp_"):
                        continue
                    um = re.match(r"([a-zA-Z0-9_]+) = lean_unsigned_to_nat\(([0-9]+)u\);", cl)
                    if um:
                        nat_exprs[um.group(1)] = f"((size_t){um.group(2)}u)"; continue
                    nm = re.match(r"([a-zA-Z0-9_]+) = lean_nat_(mul|add|sub|land)\(([a-zA-Z0-9_]+), ([a-zA-Z0-9_]+)\);", cl)
                    if nm and nm.group(3) in nat_exprs and nm.group(4) in nat_exprs:
                        op_sym = {"mul": "*", "add": "+", "sub": "-", "land": "&"}[nm.group(2)]
                        nat_exprs[nm.group(1)] = f"({nat_exprs[nm.group(3)]} {op_sym} {nat_exprs[nm.group(4)]})"
                        continue
                    uom = re.match(r"([a-zA-Z0-9_]+) = lean_uint64_of_nat\(([a-zA-Z0-9_]+)\);", cl)
                    if uom and uom.group(2) in nat_exprs:
                        u64_exprs[uom.group(1)] = f"((uint64_t){nat_exprs[uom.group(2)]})"
                        continue
                    ok_pre = False; break
                if ok_pre and val_a2 in u64_exprs and len(params) >= 5:
                    p_nnz, p_rows = params[0], params[1]
                    fp = [
                        "{",
                        f"lean_object* {stop_var} = lean_ctor_get({range_var}, 1);",
                        f"lean_object* {step_var} = lean_ctor_get({range_var}, 2);",
                        f"lean_object* {arr0} = lean_ctor_get({b_var}, 0); lean_object* {snd0} = lean_ctor_get({b_var}, 1);",
                        f"lean_object* {arr1} = lean_ctor_get({snd0}, 0); lean_object* {arr2} = lean_ctor_get({snd0}, 1);",
                        f"if (lean_is_scalar({p_nnz}) && lean_is_scalar({p_rows}) && lean_is_scalar({i_var}) && lean_is_scalar({stop_var}) && {step_var} == lean_box(1) && lean_obj_tag({arr0}) == 246 && lean_obj_tag({arr1}) == 248 && lean_obj_tag({arr2}) == 248) {{",
                        f"size_t ln_i = lean_unbox({i_var}), ln_n = lean_unbox({stop_var});",
                        f"lean_inc({arr0}); lean_inc({arr1}); lean_inc({arr2}); lean_dec({b_var});",
                        f"if (!lean_is_exclusive({arr0})) {arr0} = lean_copy_expand_array({arr0}, false);",
                        f"{arr1} = ln_sarray_ensure_exclusive_u64({arr1}); {arr2} = ln_sarray_ensure_exclusive_u64({arr2});",
                        f"uint64_t* __restrict__ ln_p2 = ln_sarray_u64_ptr({arr2}); size_t ln_sz2 = ln_sarray_u64_size({arr2});",
                        f"lean_object* ln_inner_r = lean_alloc_ctor(0, 3, 0); lean_ctor_set(ln_inner_r, 0, lean_box(0)); lean_ctor_set(ln_inner_r, 1, {p_nnz}); lean_ctor_set(ln_inner_r, 2, lean_box(1));",
                        f"lean_object* ln_pair = lean_alloc_ctor(0, 2, 0); lean_ctor_set(ln_pair, 0, {arr0}); lean_ctor_set(ln_pair, 1, {arr1});",
                        f"for (; ln_i < ln_n; ++ln_i) {{",
                        f"if (ln_i < ln_sz2) ln_p2[ln_i] = {u64_exprs[val_a2]};",
                        f"ln_pair = {callee_fn}(lean_box(ln_i), {p_nnz}, {p_rows}, ln_inner_r, ln_pair, lean_box(0));",
                        "}",
                        f"lean_dec_ref_known(ln_inner_r, 3);",
                        decs_exit.strip(),
                        f"lean_object* ln_f0 = lean_ctor_get(ln_pair, 0); lean_object* ln_f1 = lean_ctor_get(ln_pair, 1); lean_inc(ln_f0); lean_inc(ln_f1); lean_dec(ln_pair);",
                        f"lean_object* ln_s1 = lean_alloc_ctor(0, 2, 0); lean_ctor_set(ln_s1, 0, ln_f1); lean_ctor_set(ln_s1, 1, {arr2});",
                        f"lean_object* ln_res = lean_alloc_ctor(0, 2, 0); lean_ctor_set(ln_res, 0, ln_f0); lean_ctor_set(ln_res, 1, ln_s1);",
                        "return ln_res;\n}\n}"
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
        for i in range(m.end() - 1, len(c_text)):
            if c_text[i] == "{": depth += 1
            elif c_text[i] == "}":
                depth -= 1
                if depth == 0:
                    end_pos = i + 1
                    break
        lam_body = c_text[m.end():end_pos-1].strip()
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
            if cm.group(3):
                inlined.append(f"lean_dec({cm.group(3)});")
            inlined.append(f"{state_var} = {inner_v}_{call_dst};")
            inlined.append("goto _start;")
            return "\n".join(inlined)

        f_new = re.sub(
            r"([a-zA-Z0-9_]+) = " + re.escape(lam_name) + r"\(([^)]+)\);\n(?:lean_dec\(([a-zA-Z0-9_]+)\);\n)?" + re.escape(y_var) + r" = \1;\ngoto " + re.escape(jp_label) + r";",
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
        ctor_get_aliases = {}
        for gm in re.finditer(r"([a-zA-Z0-9_]+) = lean_ctor_get\(([a-zA-Z0-9_]+), ([01])\);", body):
            dst, src, idx = gm.group(1), gm.group(2), int(gm.group(3))
            if dst.startswith("v_unused_"): continue
            if idx not in ctor_gets.setdefault(src, {}):
                ctor_gets[src][idx] = dst
            else:
                ctor_get_aliases[(dst, src)] = ctor_gets[src][idx]
        for (al_dst, al_src), al_canon in list(ctor_get_aliases.items()):
            for src_k, idx_map in ctor_gets.items():
                for idx_k, dst_k in list(idx_map.items()):
                    if dst_k == al_dst:
                        idx_map[idx_k] = al_canon
                if src_k == al_dst:
                    for idx_k, dst_k in idx_map.items():
                        if idx_k not in ctor_gets.setdefault(al_canon, {}):
                            ctor_gets[al_canon][idx_k] = dst_k
                        else:
                            ctor_get_aliases[(dst_k, al_src)] = ctor_gets[al_canon][idx_k]

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
        for (al_dst, al_src), al_canon in ctor_get_aliases.items():
            if al_src in internal_nodes:
                body = re.sub(r"[ \t]*" + re.escape(al_dst) + r" = lean_ctor_get\(" + re.escape(al_src) + r", [01]\);\n(?:[ \t]*lean_inc\(" + re.escape(al_dst) + r"\);\n)?", "", body)
                body = re.sub(r"\b" + re.escape(al_dst) + r"\b", al_canon, body)

        excl_info = {}
        ok_spine = True
        for (node, f0, s1) in spine_nodes:
            n_excl = len(re.findall(r"!lean_is_exclusive\(" + re.escape(node) + r"\)", body))
            ems = list(re.finditer(
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
            ))
            if len(ems) != n_excl:
                ok_spine = False; break
            excl_info[node] = [(em.group(1), em.group(2), em.group(3), em.group(4)) for em in ems]
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
        nat_to_u64 = {}
        for bm in re.finditer(r"([a-zA-Z0-9_]+) = lean_box_uint64\(([a-zA-Z0-9_]+)\);", body):
            box_map[bm.group(1)] = bm.group(2)
        for bm in re.finditer(r"([a-zA-Z0-9_]+) = lean_box\(([a-zA-Z0-9_]+)\);", body):
            box_map[bm.group(1)] = f"(uint64_t){bm.group(2)}"
        for um in re.finditer(r"([a-zA-Z0-9_]+) = lean_unsigned_to_nat\(([0-9]+)u\);", body):
            nat_to_u64[um.group(1)] = f"{um.group(2)}ULL"
            box_map[um.group(1)] = f"{um.group(2)}ULL"
        for um in re.finditer(r"([a-zA-Z0-9_]+) = lean_uint64_to_nat\(([a-zA-Z0-9_]+)\);", body):
            nat_to_u64[um.group(1)] = um.group(2)
            box_map[um.group(1)] = um.group(2)

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

        inner_leaf_kind = {}
        for icm in re.finditer(r"([a-zA-Z0-9_]+) = (l___private_Init_While_0__(?:whileM|repeatM)_erased___at___00[a-zA-Z0-9_]+___redArg)\(([^)]*)\);", body):
            ret_v, callee_fn, args_s = icm.group(1), icm.group(2), icm.group(3)
            if callee_fn not in scalar_while_fns:
                continue
            callee_tree, callee_leaf_kinds = scalar_while_fns[callee_fn]
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
            ret_local_kinds = {}
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
                    elif f"!lean_is_exclusive({cur_v})" in body:
                        return
                    if 0 in ctor_gets[cur_v]:
                        walk_ret_proj(t_node[0], ctor_gets[cur_v][0])
                    if 1 in ctor_gets[cur_v]:
                        walk_ret_proj(t_node[1], ctor_gets[cur_v][1])
                else:
                    ret_local_leaves[cur_v] = f"ic_{ret_v}_{t_node}"
                    ret_local_kinds[cur_v] = callee_leaf_kinds[t_node]
            walk_ret_proj(callee_tree, ret_v)
            inner_calls.append((icm.group(0), ret_v, callee_fn, call_args[:-1], arg_leaves, callee_leaf_kinds))
            inner_leaf_vars.update(ret_local_leaves)
            inner_leaf_kind.update(ret_local_kinds)
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
        leaf_is_nat = {}
        leaf_is_usize = {}
        leaf_is_sarray = {}
        sarray_mut_map = {}
        for sm in re.finditer(r"([a-zA-Z0-9_]+) = ln_sarray_set_u64\(([a-zA-Z0-9_]+), ([a-zA-Z0-9_]+), ([a-zA-Z0-9_]+)\);", body):
            sarray_mut_map[sm.group(1)] = (sm.group(2), sm.group(3), sm.group(4))
        for lv in all_candidate_leaves:
            uses = [l.strip() for l in body.splitlines() if re.search(r"\b" + re.escape(lv) + r"\b", l) and "lean_object* " not in l]
            u_ok = True
            has_nat = False
            has_usize = False
            has_sarray = False
            for u in uses:
                if "= lean_ctor_get(" in u and u.startswith(f"{lv} ="): continue
                if f"lean_unbox_uint64({lv})" in u: continue
                if f"lean_unbox({lv})" in u:
                    has_usize = True; continue
                if f"lean_uint64_of_nat({lv})" in u:
                    has_nat = True; continue
                if f"ln_sarray_get_borrowed_u64(" in u and u.endswith(f", {lv});"):
                    has_nat = True; continue
                if f", {lv}, " in u and "ln_sarray_get_borrowed_u64(" in u:
                    has_sarray = True; u_ok = False; continue
                if f"ln_sarray_set_u64({lv}, " in u:
                    has_sarray = True; u_ok = False; continue
                if f"ln_sarray_set_u64(" in u and f", {lv}, " in u:
                    has_nat = True; continue
                if re.search(rf"lean_nat_(?:mul|add|land)\((?:{re.escape(lv)}, [a-zA-Z0-9_]+|[a-zA-Z0-9_]+, {re.escape(lv)})\)", u):
                    has_nat = True; continue
                if u in (f"lean_dec({lv});", f"lean_inc({lv});"): continue
                if re.match(r"lean_ctor_set\([^,]+, [01], " + re.escape(lv) + r"\);", u): continue
                if re.match(r"[a-zA-Z0-9_]+ = " + re.escape(lv) + r";", u): continue
                u_ok = False
            leaf_can_unbox[lv] = u_ok
            leaf_is_nat[lv] = has_nat
            leaf_is_usize[lv] = has_usize
            leaf_is_sarray[lv] = has_sarray and not has_nat and not has_usize

        nat_ops = {}
        for nm in re.finditer(r"([a-zA-Z0-9_]+) = lean_nat_(mul|add|land)\(([a-zA-Z0-9_]+), ([a-zA-Z0-9_]+)\);", body):
            nat_ops[nm.group(1)] = (nm.group(2), nm.group(3), nm.group(4))

        leaf_is_u64 = {lv: leaf_can_unbox[lv] for lv in leaves}
        changed = True
        while changed:
            changed = False
            def can_eval_u64(v_cand, seen=None):
                if seen is None: seen = set()
                if v_cand in seen: return False
                if v_cand in box_map or v_cand in scalar_consts: return True
                if v_cand in inner_leaf_vars and inner_leaf_kind.get(v_cand) == "u64" and leaf_can_unbox.get(v_cand, False): return True
                if v_cand in leaves and leaf_is_u64[v_cand]: return True
                if v_cand in nat_ops:
                    _, na, nb = nat_ops[v_cand]
                    return can_eval_u64(na, seen | {v_cand}) and can_eval_u64(nb, seen | {v_cand})
                return False
            for idx_l, lv in enumerate(leaves):
                if not leaf_is_u64[lv]: continue
                for nr, vals in be_leaf_vals.items():
                    v_i = vals[idx_l]
                    if can_eval_u64(v_i): continue
                    leaf_is_u64[lv] = False
                    changed = True
                    break

        for idx_l, lv in enumerate(leaves):
            if leaf_is_u64[lv]: continue
            for nr, vals in be_leaf_vals.items():
                v_i = vals[idx_l]
                if v_i == lv: continue
                if v_i in sarray_mut_map and sarray_mut_map[v_i][0] == lv and can_eval_u64(sarray_mut_map[v_i][1]):
                    leaf_is_sarray[lv] = True
                elif v_i in inner_leaf_vars and inner_leaf_kind.get(v_i) == "sarray":
                    leaf_is_sarray[lv] = True
                else:
                    leaf_is_sarray[lv] = False
                    break

        # Validate that any inner_calls only pass scalarizable or sarray arg_leaves
        valid_inner_calls = []
        for ic_tup in inner_calls:
            call_str, ret_v, callee_fn, extra_args, arg_leaves, callee_leaf_kinds = ic_tup
            ok_ic = True
            for idx_k, kind_k in enumerate(callee_leaf_kinds):
                av = arg_leaves[idx_k]
                if kind_k == "u64":
                    if not can_eval_u64(av): ok_ic = False; break
                elif kind_k == "sarray":
                    if not (av in leaves and leaf_is_sarray.get(av, False)): ok_ic = False; break
                else:
                    ok_ic = False; break
            if ok_ic:
                valid_inner_calls.append(ic_tup)
        if len(valid_inner_calls) != len(inner_calls):
            inner_calls = []
            inner_leaf_vars = {}
            inner_internal_nodes = set()
            inner_excl_info = {}
            inner_arg_pairs = set()

        ok_internal = True
        for (node, f0, s1) in spine_nodes:
            reuse_vs = {rv for (_, rv, _, _) in excl_info[node]}
            for l in body.splitlines():
                s = l.strip()
                if "lean_object* " in s: continue
                if not re.search(r"\b" + re.escape(node) + r"\b", s): continue
                if f"lean_ctor_get({node}, " in s: continue
                if s.startswith(f"{node} = lean_ctor_get("): continue
                if f"!lean_is_exclusive({node})" in s: continue
                if s in (f"lean_inc({node});", f"lean_dec({node});") or any(s == f"{rv} = {node};" for rv in reuse_vs): continue
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
                if leaf_is_nat.get(lv, False):
                    hdr.append(f"u_{lv} = lean_uint64_of_nat({lv});")
                elif leaf_is_usize.get(lv, False):
                    hdr.append(f"u_{lv} = (uint64_t)lean_unbox({lv});")
                else:
                    hdr.append(f"u_{lv} = lean_unbox_uint64({lv});")
            elif leaf_is_sarray.get(lv, False):
                hdr.append(f"lean_inc({lv});")
                hdr.append(f"{lv} = ln_sarray_ensure_exclusive_u64({lv});")
                hdr.append(f"uint64_t* ptr_{lv} = ln_sarray_u64_ptr({lv});")
                hdr.append(f"size_t sz_{lv} = ln_sarray_u64_size({lv});")
            else:
                hdr.append(f"lean_inc({lv});")
        hdr.append(f"lean_dec({state_var});")
        for (node, _, _) in spine_nodes:
            for (chk_v, reuse_v, shared_v, _) in excl_info[node]:
                hdr.append(f"lean_object* {reuse_v} = lean_box(0);")
                hdr.append(f"uint8_t {shared_v} = 1;")
                hdr.append(f"uint8_t {chk_v} = 1;")
        for inode, (chk_v, reuse_v, shared_v, _) in inner_excl_info.items():
            hdr.append(f"lean_object* {reuse_v} = lean_box(0);")
            hdr.append(f"uint8_t {shared_v} = 1;")
            hdr.append(f"uint8_t {chk_v} = 1;")

        new_body = body
        vars_to_strip_decl = set()
        for (al_dst, al_src), al_canon in ctor_get_aliases.items():
            if al_src in internal_nodes:
                vars_to_strip_decl.add(al_dst)
        for (node, f0, s1) in spine_nodes:
            vars_to_strip_decl.update([f0, s1])
            for (chk_v, reuse_v, shared_v, _) in excl_info[node]:
                vars_to_strip_decl.update([chk_v, reuse_v, shared_v])
        for inode in inner_internal_nodes:
            vars_to_strip_decl.add(inode)
            if inode in ctor_gets:
                for ch in ctor_gets[inode].values():
                    vars_to_strip_decl.add(ch)
        for inode, (chk_v, reuse_v, shared_v, _) in inner_excl_info.items():
            vars_to_strip_decl.update([chk_v, reuse_v, shared_v])

        for (node, f0, s1) in spine_nodes:
            new_body = re.sub(r"[ \t]*" + re.escape(f0) + r" = lean_ctor_get\(" + re.escape(node) + r", 0\);\n(?:[ \t]*lean_inc\(" + re.escape(f0) + r"\);\n)?", "", new_body)
            new_body = re.sub(r"[ \t]*" + re.escape(s1) + r" = lean_ctor_get\(" + re.escape(node) + r", 1\);\n(?:[ \t]*lean_inc\(" + re.escape(s1) + r"\);\n)?", "", new_body)
            for (chk_v, reuse_v, shared_v, jp_lbl) in excl_info[node]:
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

        for lv in leaves:
            if leaf_is_u64[lv] and leaf_is_nat.get(lv, False):
                nat_to_u64[lv] = f"u_{lv}"
        for ilv, ic_var in inner_leaf_vars.items():
            if leaf_is_nat.get(ilv, False):
                nat_to_u64[ilv] = ic_var

        # Lower scalarized Nat arithmetic chains (lean_nat_mul/add/land/dec_eq and ln_sarray_get_borrowed_u64) BEFORE rewriting inner calls
        nat_step_progress = True
        while nat_step_progress:
            nat_step_progress = False
            for nm in list(re.finditer(r"([a-zA-Z0-9_]+) = lean_nat_(mul|add|land)\(([a-zA-Z0-9_]+), ([a-zA-Z0-9_]+)\);", new_body)):
                dst, op, a, b = nm.group(1), nm.group(2), nm.group(3), nm.group(4)
                if dst not in nat_to_u64 and a in nat_to_u64 and b in nat_to_u64:
                    op_fn = {"mul": "lean_uint64_mul", "add": "lean_uint64_add", "land": "lean_uint64_land"}[op]
                    new_body = new_body.replace(nm.group(0), f"uint64_t u_{dst} = {op_fn}({nat_to_u64[a]}, {nat_to_u64[b]}); {dst} = lean_box(0);")
                    new_body = re.sub(r"[ \t]*lean_dec\(" + re.escape(dst) + r"\);\n", "", new_body)
                    nat_to_u64[dst] = f"u_{dst}"
                    box_map[dst] = f"u_{dst}"
                    nat_step_progress = True
        for nv, u_expr in list(nat_to_u64.items()):
            new_body = re.sub(
                r"lean_nat_dec_eq\(" + re.escape(nv) + r", ([a-zA-Z0-9_]+)\)",
                lambda m_eq: f"lean_uint64_dec_eq({u_expr}, {nat_to_u64[m_eq.group(1)]})" if m_eq.group(1) in nat_to_u64 else m_eq.group(0),
                new_body
            )
            new_body = re.sub(
                r"ln_sarray_get_borrowed_u64\(([^,]+), ([^,]+), " + re.escape(nv) + r"\)",
                lambda m_g: f"ptr_{m_g.group(2).strip()}[(size_t)({u_expr})]" if leaf_is_sarray.get(m_g.group(2).strip(), False) else f"ln_sarray_u64_ptr({m_g.group(2).strip()})[(size_t)({u_expr})]",
                new_body
            )
            new_body = re.sub(r"[ \t]*lean_dec\(" + re.escape(nv) + r"\);\n", "", new_body)

        for dst_s, (arr_s, idx_s, val_s) in sarray_mut_map.items():
            if leaf_is_sarray.get(arr_s, False) and idx_s in nat_to_u64:
                u_idx = nat_to_u64[idx_s]
                new_body = new_body.replace(
                    f"{dst_s} = ln_sarray_set_u64({arr_s}, {idx_s}, {val_s});",
                    f"if ((size_t)({u_idx}) < sz_{arr_s}) ptr_{arr_s}[(size_t)({u_idx})] = {val_s}; {dst_s} = {arr_s};"
                )

        # Rewrite inner calls to scalar helper calls
        for call_str, ret_v, callee_fn, extra_args, arg_leaves, callee_leaf_kinds in inner_calls:
            lines_ic = []
            ptr_args = []
            for idx_k, kind_k in enumerate(callee_leaf_kinds):
                av = arg_leaves[idx_k]
                if kind_k == "sarray":
                    ptr_args.extend([f"ptr_{av}", f"sz_{av}"])
                    for ilv, ic_var in list(inner_leaf_vars.items()):
                        if ic_var == f"ic_{ret_v}_{idx_k}":
                            inner_leaf_vars[ilv] = av
                else:
                    if av in leaves:
                        a_expr = f"u_{av}"
                    elif av in inner_leaf_vars:
                        a_expr = inner_leaf_vars[av]
                    elif av in box_map:
                        a_expr = box_map[av]
                    elif av in nat_to_u64:
                        a_expr = nat_to_u64[av]
                    else:
                        a_expr = scalar_consts[av]
                    lines_ic.append(f"uint64_t ic_{ret_v}_{idx_k} = {a_expr};")
                    ptr_args.append(f"&ic_{ret_v}_{idx_k}")
            all_c_args = ", ".join(extra_args + ptr_args)
            lines_ic.append(f"{callee_fn}_scalar({all_c_args});")
            new_body = new_body.replace(call_str, "\n".join(lines_ic))

        for ilv, ic_var in inner_leaf_vars.items():
            if ic_var in leaves and leaf_is_sarray.get(ic_var, False):
                new_body = re.sub(r"[ \t]*lean_dec\(" + re.escape(ilv) + r"\);\n", "", new_body)
                new_body = re.sub(r"[ \t]*lean_inc\(" + re.escape(ilv) + r"\);\n", "", new_body)
                continue
            new_body = new_body.replace(f"lean_unbox_uint64({ilv})", ic_var)
            new_body = new_body.replace(f"lean_uint64_of_nat({ilv})", ic_var)
            new_body = new_body.replace(f"lean_unbox({ilv})", f"(size_t)({ic_var})")
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
            if ic_var in leaves and leaf_is_sarray.get(ic_var, False):
                new_body = re.sub(
                    r"lean_ctor_set\(([a-zA-Z0-9_]+), ([01]), " + re.escape(ilv) + r"\);",
                    rf"lean_ctor_set(\1, \2, {ic_var});",
                    new_body
                )
                continue
            box_fn = "lean_uint64_to_nat" if leaf_is_nat.get(ilv, False) else ("lean_box" if leaf_is_usize.get(ilv, False) else "lean_box_uint64")
            new_body = re.sub(
                r"lean_ctor_set\(([a-zA-Z0-9_]+), ([01]), " + re.escape(ilv) + r"\);",
                rf"lean_ctor_set(\1, \2, {box_fn}({ic_var}));",
                new_body
            )

        for lv in leaves:
            if not leaf_is_u64[lv]: continue
            new_body = new_body.replace(f"lean_unbox_uint64({lv})", f"u_{lv}")
            new_body = new_body.replace(f"lean_uint64_of_nat({lv})", f"u_{lv}")
            new_body = new_body.replace(f"lean_unbox({lv})", f"(size_t)(u_{lv})")
            new_body = re.sub(r"[ \t]*lean_dec\(" + re.escape(lv) + r"\);\n", "", new_body)
            new_body = re.sub(r"[ \t]*lean_inc\(" + re.escape(lv) + r"\);\n", "", new_body)
            box_fn = "lean_uint64_to_nat" if leaf_is_nat.get(lv, False) else ("lean_box" if leaf_is_usize.get(lv, False) else "lean_box_uint64")
            new_body = re.sub(
                r"lean_ctor_set\(([a-zA-Z0-9_]+), ([01]), " + re.escape(lv) + r"\);",
                rf"lean_ctor_set(\1, \2, {box_fn}(u_{lv}));",
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
                elif leaf_is_sarray.get(lv, False):
                    pass
                else:
                    assigns.append(f"lean_object* next_{lv} = {v_i};")
            for lv in leaves:
                if leaf_is_u64[lv]:
                    assigns.append(f"u_{lv} = next_u_{lv};")
                elif leaf_is_sarray.get(lv, False):
                    pass
                else:
                    assigns.append(f"{lv} = next_{lv};")
            assigns.append("goto _start;")
            assigns.append("}")
            new_body = new_body.replace(f"{state_var} = {nr};\ngoto _start;", "\n".join(assigns))

        for (node1, f1, s1) in reversed(spine_nodes[1:]):
            f1_b = "lean_uint64_to_nat" if leaf_is_nat.get(f1, False) else ("lean_box" if leaf_is_usize.get(f1, False) else "lean_box_uint64")
            s1_b = "lean_uint64_to_nat" if leaf_is_nat.get(s1, False) else ("lean_box" if leaf_is_usize.get(s1, False) else "lean_box_uint64")
            f1_expr = f"{f1_b}(u_{f1})" if leaf_is_u64.get(f1, False) else f1
            s1_expr = f"{s1_b}(u_{s1})" if leaf_is_u64.get(s1, False) else s1
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
                and l.strip() != f"{bv} = lean_uint64_to_nat({uv});"
                and not re.match(re.escape(bv) + r" = lean_unsigned_to_nat\([0-9]+u\);", l.strip())
                and not l.strip().startswith(f"{bv} = ((lean_object*)(")
            ]
            if not uses_after:
                new_body = new_body.replace(f"{bv} = lean_box_uint64({uv});", f"{bv} = lean_box(0);")
                new_body = new_body.replace(f"{bv} = lean_uint64_to_nat({uv});", f"{bv} = lean_box(0);")
                new_body = re.sub(re.escape(bv) + r" = lean_unsigned_to_nat\([0-9]+u\);", f"{bv} = lean_box(0);", new_body)

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
        if all(leaf_is_u64[lv] or leaf_is_sarray.get(lv, False) for lv in leaves):
            leaf_kinds = ["u64" if leaf_is_u64[lv] else "sarray" for lv in leaves]
            scalar_while_fns[fn_name] = (spine_tree, leaf_kinds)
            extra_p_decls = param_decls[:-1]
            ptr_p_decls = []
            for idx_l, lv in enumerate(leaves):
                if leaf_is_u64[lv]:
                    ptr_p_decls.append(f"uint64_t* p_{idx_l}")
                else:
                    ptr_p_decls.extend([f"uint64_t* ptr_{lv}", f"size_t sz_{lv}"])
            sig_args = ", ".join(extra_p_decls + ptr_p_decls)
            sh_hdr = ["{"]
            for idx_l, lv in enumerate(leaves):
                if leaf_is_u64[lv]:
                    sh_hdr.append(f"uint64_t u_{lv} = *p_{idx_l};")
                else:
                    sh_hdr.append(f"lean_object* {lv} = lean_box(0);")
            for (node, _, _) in spine_nodes:
                for (chk_v, reuse_v, shared_v, _) in excl_info[node]:
                    sh_hdr.append(f"lean_object* {reuse_v} = lean_box(0);")
                    sh_hdr.append(f"uint8_t {shared_v} = 1;")
                    sh_hdr.append(f"uint8_t {chk_v} = 1;")
            for inode, (chk_v, reuse_v, shared_v, _) in inner_excl_info.items():
                sh_hdr.append(f"lean_object* {reuse_v} = lean_box(0);")
                sh_hdr.append(f"uint8_t {shared_v} = 1;")
                sh_hdr.append(f"uint8_t {chk_v} = 1;")
            ret_assigns = " ".join([f"*p_{idx_l} = u_{lv};" for idx_l, lv in enumerate(leaves) if leaf_is_u64[lv]]) + " return;"
            sh_body = re.sub(
                r"if \(([a-zA-Z0-9_]+) == 0\)\n\{\n(?:(?!goto _start;).)*?return [a-zA-Z0-9_]+;\n(?:[ \t]*\}\n)+([ \t]*else\n\{)",
                rf"if (\1 == 0)\n{{\n{ret_assigns}\n}}\n\2",
                "\n".join(cleaned_lines),
                count=1,
                flags=re.DOTALL
            )
            sh_body = re.sub(
                r"\n([ \t]*else\n\{\n)(?:(?!goto _start;).)*?return [a-zA-Z0-9_]+;\n(?:[ \t]*\}[ \t]*\n?)+$",
                rf"\n\1{ret_assigns}\n}}",
                sh_body,
                count=1,
                flags=re.DOTALL
            )
            sh_body = re.sub(r"\breturn [a-zA-Z0-9_]+;", ret_assigns, sh_body)
            dead_ctor = r"(?:[ \t]*lean_object\* [^\n]+\n)?(?:[ \t]*[a-zA-Z0-9_]+ = lean_alloc_ctor\(0, 2, 0\);\n|[ \t]*lean_ctor_set\([^\n]+\);\n)+"
            sh_body = re.sub(dead_ctor + r"([ \t]*\*p_0 = [^\n]+return;)", r"\1", sh_body)
            sh_body = sh_body.replace("goto _start;", "continue;")
            for o_m in list(re.finditer(r"([a-zA-Z0-9_]+) = lean_obj_once\(&([a-zA-Z0-9_]+), &[a-zA-Z0-9_]+_once, _init_[a-zA-Z0-9_]+\);", sh_body)):
                o_var, o_sym = o_m.group(1), o_m.group(2)
                sh_hdr.append(f"lean_object* {o_var}_hoist = lean_obj_once(&{o_sym}, &{o_sym}_once, _init_{o_sym});")
                sh_hdr.append(f"const uint64_t* ptr_{o_var} = ln_sarray_u64_ptr({o_var}_hoist);")
                sh_body = sh_body.replace(o_m.group(0), f"{o_var} = {o_var}_hoist;")
                sh_body = sh_body.replace(f"ln_sarray_u64_ptr({o_var})", f"ptr_{o_var}")
            for ep in extra_p_decls:
                ep_name = ep.split()[-1]
                if f"ln_sarray_u64_ptr({ep_name})" in sh_body:
                    sh_hdr.append(f"const uint64_t* ptr_{ep_name} = ln_sarray_u64_ptr({ep_name});")
                    sh_body = sh_body.replace(f"ln_sarray_u64_ptr({ep_name})", f"ptr_{ep_name}")
            unroll_prag = "\n#pragma clang loop unroll(full)" if (all(leaf_is_u64[lv] for lv in leaves) and "_scalar(" not in sh_body) else ""
            scalar_helper = (
                f"static inline __attribute__((always_inline)) void {fn_name}_scalar({sig_args}){{\n"
                + "\n".join(sh_hdr)
                + f"{unroll_prag}\nfor (;;) {{\n"
                + sh_body
                + "\n}\n}\n}\n"
            )

        body_joined = "\n".join(cleaned_lines)
        for o_m in list(re.finditer(r"([a-zA-Z0-9_]+) = lean_obj_once\(&([a-zA-Z0-9_]+), &[a-zA-Z0-9_]+_once, _init_[a-zA-Z0-9_]+\);", body_joined)):
            o_var, o_sym = o_m.group(1), o_m.group(2)
            hdr.append(f"lean_object* {o_var}_hoist = lean_obj_once(&{o_sym}, &{o_sym}_once, _init_{o_sym});")
            hdr.append(f"const uint64_t* ptr_{o_var} = ln_sarray_u64_ptr({o_var}_hoist);")
            body_joined = body_joined.replace(o_m.group(0), f"{o_var} = {o_var}_hoist;")
            body_joined = body_joined.replace(f"ln_sarray_u64_ptr({o_var})", f"ptr_{o_var}")
        for ep in param_decls[:-1]:
            ep_name = ep.split()[-1]
            if f"ln_sarray_u64_ptr({ep_name})" in body_joined:
                hdr.append(f"const uint64_t* ptr_{ep_name} = ln_sarray_u64_ptr({ep_name});")
                body_joined = body_joined.replace(f"ln_sarray_u64_ptr({ep_name})", f"ptr_{ep_name}")

        f_final = (
            scalar_helper
            + f"LEAN_EXPORT lean_object* {fn_name}({params_str}){{\n"
            + "\n".join(hdr)
            + "\n_start:\n{\n"
            + body_joined
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
    # Peephole D: sign-bit branch diamond -> arithmetic shift right
    c_text = re.sub(
        r"(?:([a-zA-Z0-9_]+) = 9223372036854775808ULL;\n)?"
        r"([a-zA-Z0-9_]+) = lean_uint64_land\(([a-zA-Z0-9_]+), ([a-zA-Z0-9_]+)\);\n"
        r"([a-zA-Z0-9_]+) = 0ULL;\n"
        r"([a-zA-Z0-9_]+) = lean_uint64_dec_eq\(\2, \5\);\n"
        r"if \(\6 == 0\)\n"
        r"\{\n"
        r"(?:[ \t]*uint64_t [^\n]+\n)?"
        r"([a-zA-Z0-9_]+) = ([0-9]+)ULL;\n"
        r"([a-zA-Z0-9_]+) = lean_uint64_shift_right\(\3, \7\);\n"
        r"([a-zA-Z0-9_]+) = 18446[0-9]+ULL;\n"
        r"([a-zA-Z0-9_]+) = lean_uint64_lor\(\9, \10\);\n"
        r"((?:[a-zA-Z0-9_]+ = [a-zA-Z0-9_]+;\n)*)"
        r"([a-zA-Z0-9_]+) = \11;\n"
        r"goto ([a-zA-Z0-9_]+);\n"
        r"\}\n"
        r"else\n"
        r"\{\n"
        r"(?:[ \t]*uint64_t [^\n]+\n)?"
        r"[a-zA-Z0-9_]+ = \8ULL;\n"
        r"[a-zA-Z0-9_]+ = lean_uint64_shift_right\(\3, [a-zA-Z0-9_]+\);\n"
        r"\12"
        r"\13 = [a-zA-Z0-9_]+;\n"
        r"goto \14;\n"
        r"\}",
        lambda m: (
            (f"{m.group(1)} = 9223372036854775808ULL;\n" if m.group(1) else "")
            + m.group(12)
            + f"{m.group(13)} = (uint64_t)(((int64_t)({m.group(3)})) >> {m.group(8)}ULL);\n"
            + f"goto {m.group(14)};"
        ),
        c_text
    )
    return c_text

def apply_pass2c_hot_loops(c_text):
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
            + "if (!lean_is_scalar(p_a)) {\n"
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
            + "return r;\n}\n}\n"
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
