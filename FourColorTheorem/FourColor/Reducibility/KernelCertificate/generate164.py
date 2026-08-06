#!/usr/bin/env python3
"""Untrusted compact-certificate generator for configuration 164."""

from __future__ import annotations

import pathlib
import shutil
import sys
import time
from collections import Counter
from itertools import product


HEIGHT = 12
PERMUTATIONS = (
    (1, 2, 3),
    (1, 3, 2),
    (2, 1, 3),
    (2, 3, 1),
    (3, 1, 2),
    (3, 2, 1),
)
PERMUTATION_ORDER = (4, 3, 0, 1, 2, 5)
MODULE_ROOT = (
    "FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164Data"
)
SEGMENT_MODULE_ROOT = (
    "FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164SegmentData"
)
OWNER_MODULE_ROOT = (
    "FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164OwnerData"
)
OWNER_CHECK_ROOT = (
    "FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164OwnerChecks"
)
OWNER_ENTRY_ROOT = (
    "FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164OwnerEntryData"
)
PROGRAM_DATA_ROOT = (
    "FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramData"
)
PROGRAM_CHECK_ROOT = (
    "FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164ProgramChecks"
)
CORE_IMPORT = (
    "FourColorTheorem.FourColor.Reducibility.KernelCertificate.IndexedReplay"
)
CONFIG164_PROGRAM = (
    ("rotate", 35), "h", ("rotate", 3), "h", ("rotate", 11), "h",
    ("rotate", 1), "y", ("rotate", 4), "h", ("rotate", 3), "h",
    ("rotate", 10), "h", ("rotate", 1), "y", ("rotate", 3), "h",
    ("rotate", 10), "y", ("rotate", 2), "h", ("rotate", 1), "y",
    ("rotate", 3), "h", ("rotate", 8), "y", "y", ("rotate", 1),
    "y", ("rotate", 1), "y", ("rotate", 3), "y", "y", "y",
)
REPLAY_STEPS = (
    "u", ("rotate", 3), "y", ("rotate", 1), "y", ("rotate", 1),
    "y", "y", ("rotate", 8), "h", ("rotate", 3), "y",
    ("rotate", 1), "h", ("rotate", 2), "y", ("rotate", 10), "h",
    ("rotate", 3), "y", ("rotate", 1), "h", ("rotate", 10), "h",
    ("rotate", 3), "h", ("rotate", 4), "y", ("rotate", 1), "h",
    ("rotate", 11), "h", ("rotate", 3), "h",
)


def decode_trace(code: int) -> tuple[int, ...]:
    trace = []
    for _ in range(HEIGHT):
        trace.append(code % 3 + 1)
        code //= 3
    return tuple(trace)


def encode_trace(trace: tuple[int, ...]) -> int:
    code = 0
    place = 1
    for color in trace:
        code += (color - 1) * place
        place *= 3
    return code


def apply_color_permutation(trace: tuple[int, ...], tag: int) -> tuple[int, ...]:
    table = PERMUTATIONS[tag]
    return tuple(table[color - 1] for color in trace)


def trace_ttail(trace: tuple[int, ...]) -> tuple[int, ...]:
    if not trace or trace[0] == 0:
        return (0,)
    edge_rotation = (0, 0, 4, 3)[trace[0]]
    return apply_color_permutation(trace[1:], edge_rotation)


def trace_etail(trace: tuple[int, ...]) -> tuple[int, ...]:
    normalized = trace_ttail(trace)
    for color in normalized:
        if color == 2:
            return normalized
        if color == 3:
            return apply_color_permutation(normalized, 1)
    return normalized


def rotate_left(trace: tuple[int, ...], amount: int) -> tuple[int, ...]:
    if len(trace) <= amount:
        return trace
    return trace[amount:] + trace[:amount]


def add_witness_state(
    states: dict[tuple[int, ...], tuple[int, int]],
    trace: tuple[int, ...], witness: int, place: int,
) -> None:
    states.setdefault(trace, (witness, place))


def advance_witness_states(
    states: dict[tuple[int, ...], tuple[int, int]], step,
) -> dict[tuple[int, ...], tuple[int, int]]:
    result: dict[tuple[int, ...], tuple[int, int]] = {}
    for trace, (witness, place) in states.items():
        if isinstance(step, tuple):
            add_witness_state(
                result, rotate_left(trace, step[1]), witness, place
            )
        elif step == "y":
            if not trace:
                continue
            head, tail = trace[0], trace[1:]
            p231 = PERMUTATIONS[3][head - 1]
            p312 = PERMUTATIONS[4][head - 1]
            add_witness_state(
                result, (p231, p312) + tail, witness, place * 2
            )
            add_witness_state(
                result, (p312, p231) + tail, witness + place, place * 2
            )
        elif step == "h":
            if len(trace) < 2:
                continue
            first, second, tail = trace[0], trace[1], trace[2:]
            if first == second:
                p231 = PERMUTATIONS[3][first - 1]
                p312 = PERMUTATIONS[4][first - 1]
                add_witness_state(
                    result, (p231, p231) + tail, witness, place * 2
                )
                add_witness_state(
                    result, (p312, p312) + tail,
                    witness + place, place * 2,
                )
            else:
                add_witness_state(
                    result, (second, first) + tail, witness, place
                )
        elif step == "u":
            for color in (1, 2, 3):
                add_witness_state(
                    result, (color, color) + trace, witness, place
                )
        else:
            raise RuntimeError(f"unsupported configuration-164 step: {step}")
    return result


def configuration164_base_witnesses(base_codes: list[int]) -> list[int]:
    program = list(reversed(CONFIG164_PROGRAM))
    if not program or program[0] != "y":
        raise RuntimeError("configuration 164 no longer has the expected initial Y")
    states: dict[tuple[int, ...], tuple[int, int]] = {
        (1, 2, 3): (0, 1)
    }
    for step in program[1:]:
        states = advance_witness_states(states, step)
    outputs: dict[tuple[int, ...], int] = {}
    for trace, (witness, _) in states.items():
        output = trace_etail(trace[1:])
        if 0 not in output:
            outputs.setdefault(output, witness)
    witnesses = []
    for code in base_codes:
        output = trace_ttail(decode_trace(code))
        witness = outputs.get(output)
        if witness is None:
            raise RuntimeError(f"no base witness for trace code {code}")
        witnesses.append(witness)
    return witnesses


def permute(trace: tuple[int, ...], tag: int) -> tuple[int, ...]:
    table = PERMUTATIONS[tag]
    return tuple(table[color - 1] for color in trace)


def even_trace(trace: tuple[int, ...]) -> bool:
    head, tail = trace[0], trace[1:]
    edge_rotation = PERMUTATIONS[(0, 0, 4, 3)[head]]
    normalized = tuple(edge_rotation[color - 1] for color in tail)
    for color in normalized:
        if color == 2:
            return True
        if color == 3:
            return False
    return True


def valid_trace(trace: tuple[int, ...]) -> bool:
    total = 0
    for color in trace:
        total ^= color
    return total != 0 and even_trace(trace)


def matching_words(
    trace: tuple[int, ...],
    visit,
    index: int = 0,
    stack: tuple[bool, ...] = (),
    parity: bool = False,
    word_code: int = 0,
    place: int = 1,
) -> bool:
    """Visit valid partial chromograms; stop when visit returns False."""
    if index == HEIGHT:
        if len(stack) == 1 or (not stack and parity):
            return visit(word_code)
        return True

    color = trace[index]
    next_place = place * 4
    if color == 1:
        return matching_words(
            trace, visit, index + 1, stack, not parity,
            word_code + place, next_place,
        )

    pushed = color == 3
    if not matching_words(
        trace, visit, index + 1, (pushed,) + stack, parity,
        word_code, next_place,
    ):
        return False

    if not stack:
        return True
    top, rest = stack[0], stack[1:]
    if color == 2:
        symbol = 3 if top else 2
    else:
        symbol = 2 if top else 3
    return matching_words(
        trace, visit, index + 1, rest,
        parity ^ (symbol == 3), word_code + symbol * place, next_place,
    )


def add_hits(
    trace: tuple[int, ...], hit_words: dict[int, int], owner: int
) -> None:
    def add(word: int) -> bool:
        hit_words.setdefault(word, owner)
        return True

    matching_words(trace, add)


def add_earliest_hits(
    trace: tuple[int, ...], owners: dict[int, int], owner: int
) -> None:
    def add(word: int) -> bool:
        owners.setdefault(word, owner)
        return True

    matching_words(trace, add)


def covering_witnesses(
    trace: tuple[int, ...], hit_words: dict[int, int]
) -> list[int] | None:
    witnesses: list[int] = []

    def witness(word: int) -> bool:
        owner = hit_words.get(word)
        if owner is None:
            return False
        witnesses.append(owner)
        return True

    if matching_words(trace, witness):
        return witnesses
    return None


def covered(trace: tuple[int, ...], hit_words: dict[int, int]) -> bool:
    return matching_words(trace, lambda word: word in hit_words)


def find_permutation(
    trace: tuple[int, ...], hit_words: dict[int, int]
) -> tuple[int, list[int]] | None:
    for tag in PERMUTATION_ORDER:
        witnesses = covering_witnesses(permute(trace, tag), hit_words)
        if witnesses is not None:
            return tag, witnesses
    return None


def read_codes(path: pathlib.Path) -> set[int]:
    return {int(line) for line in path.read_text().splitlines() if line}


def nat_tree_expr(values: list[str], sizes: list[int] | None = None) -> str:
    if not values:
        return "NatTree.empty"
    if sizes is None:
        sizes = [1] * len(values)
        values = [f"NatTree.leaf {value}" for value in values]
    if len(values) == 1:
        return values[0]
    split = len(values) // 2
    left = nat_tree_expr(values[:split], sizes[:split])
    right = nat_tree_expr(values[split:], sizes[split:])
    return f"NatTree.node {sum(sizes[:split])} ({left}) ({right})"


def lean_module(imports: list[str], body: str) -> str:
    return (
        "".join(f"import {module}\n" for module in imports)
        + "\nnamespace Schematic.Math.GraphTheory.FourColor.KernelCertificate\n\n"
        + body
        + "\nend Schematic.Math.GraphTheory.FourColor.KernelCertificate\n"
    )


def write_source_tree(
    directory: pathlib.Path, codes: list[int], base_count: int,
    block_size: int = 256, blocks_per_module: int = 16,
) -> None:
    blocks = []
    definitions: list[str] = []
    modules: list[str] = []
    for start in range(0, len(codes), block_size):
        block = codes[start:start + block_size]
        name = f"config164SourceBlock{start // block_size:04d}"
        definitions.append(
            f"def {name} : NatTree :=\n  "
            + nat_tree_expr([str(code) for code in block])
            + "\n"
        )
        blocks.append(name)
    for start in range(0, len(definitions), blocks_per_module):
        index = start // blocks_per_module
        name = f"SourceBlocks{index:03d}"
        modules.append(name)
        (directory / f"{name}.lean").write_text(lean_module(
            [CORE_IMPORT], "\n".join(definitions[start:start + blocks_per_module])
        ))

    def local_index(index: int) -> str:
        return "index" if index == 0 else f"(index - {index})"

    def dispatch(
        name: str, children: list[str], stride: int, use_tree_get: bool,
    ) -> str:
        cases = []
        for index, child in enumerate(children):
            argument = local_index(index * stride)
            expression = (
                f"NatTree.get {child} {argument}" if use_tree_get
                else f"{child} {argument}"
            )
            cases.append(f"  | {index} => {expression}")
        return (
            f"def {name} (index : Nat) : Option Nat :=\n"
            f"  match index / {stride} with\n"
            + "\n".join(cases)
            + "\n  | _ => none\n"
        )

    dispatch_definitions = []
    group_size = 8
    group_names = []
    for start in range(0, len(blocks), group_size):
        name = f"config164SourceGroup{start // group_size:03d}"
        group_names.append(name)
        dispatch_definitions.append(
            dispatch(name, blocks[start:start + group_size], block_size, True)
        )
    page_size = 8
    page_names = []
    group_stride = block_size * group_size
    for start in range(0, len(group_names), page_size):
        name = f"config164SourcePage{start // page_size:03d}"
        page_names.append(name)
        dispatch_definitions.append(dispatch(
            name, group_names[start:start + page_size], group_stride, False
        ))
    page_stride = group_stride * page_size
    source_body = (
        f"def config164BaseCount : Nat := {base_count}\n\n"
        f"def config164SourceCount : Nat := {len(codes)}\n\n"
        + "\n".join(dispatch_definitions)
        + "\n"
        + dispatch("config164Source", page_names, page_stride, False)
    )
    (directory / "Source.lean").write_text(lean_module(
        [f"{MODULE_ROOT}.{name}" for name in modules], source_body
    ))


def ref_trie_expr(refs: dict[tuple[int, ...], int], depth: int) -> str:
    if not refs:
        return "RefTrie.empty"
    if depth == 0:
        ref = refs[()]
        return (
            f"RefTrie.node (some {ref}) RefTrie.empty RefTrie.empty "
            "RefTrie.empty"
        )
    children = []
    for color in (1, 2, 3):
        child_refs = {
            trace[1:]: ref for trace, ref in refs.items() if trace[0] == color
        }
        children.append(ref_trie_expr(child_refs, depth - 1))
    return (
        "RefTrie.node none "
        + " ".join(f"({child})" for child in children)
    )


def decode_word(code: int) -> tuple[int, ...]:
    word = []
    for _ in range(HEIGHT):
        word.append(code % 4)
        code //= 4
    return tuple(word)


def owner_trie_expr(refs: dict[tuple[int, ...], int], depth: int) -> str:
    if not refs:
        return "OwnerTrie.empty"
    if depth == 0:
        return (
            f"OwnerTrie.node (some {refs[()]}) OwnerTrie.empty "
            "OwnerTrie.empty OwnerTrie.empty OwnerTrie.empty"
        )
    children = []
    for symbol in range(4):
        child_refs = {
            word[1:]: ref for word, ref in refs.items() if word[0] == symbol
        }
        children.append(owner_trie_expr(child_refs, depth - 1))
    return (
        "OwnerTrie.node none "
        + " ".join(f"({child})" for child in children)
    )


def gram_symbol(symbol: int) -> str:
    return (
        "GramSymbol.push", "GramSymbol.skip",
        "GramSymbol.pop0", "GramSymbol.pop1",
    )[symbol]


def write_owner_certificate(
    root: pathlib.Path,
    entries: list[tuple[int, int, list[int], list[int]]],
    source_codes: list[int],
    prefix_depth: int = 6,
    prefixes_per_module: int = 16,
    entry_segment_size: int = 128,
) -> list[int]:
    owners: dict[int, int] = {}
    for ref, code in enumerate(source_codes):
        add_earliest_hits(decode_trace(code), owners, ref)
    owner_refs = {decode_word(word): ref for word, ref in owners.items()}

    data_directory = root / "Config164OwnerData"
    check_directory = root / "Config164OwnerChecks"
    entry_directory = root / "Config164OwnerEntryData"
    for directory in (data_directory, check_directory, entry_directory):
        directory.mkdir(parents=True, exist_ok=True)
        for stale in directory.glob("*.lean"):
            stale.unlink()

    buckets: dict[tuple[int, ...], dict[tuple[int, ...], int]] = {}
    for word, ref in owner_refs.items():
        prefix = word[:prefix_depth]
        buckets.setdefault(prefix, {})[word[prefix_depth:]] = ref

    bucket_items = sorted(buckets.items())
    definitions: list[str] = []
    bucket_names: dict[tuple[int, ...], str] = {}
    for prefix, suffix_refs in bucket_items:
        suffix = "".join(map(str, prefix))
        name = f"config164OwnerTrie{suffix}"
        bucket_names[prefix] = name
        definitions.append(
            f"def {name} : OwnerTrie :=\n  "
            + owner_trie_expr(suffix_refs, HEIGHT - prefix_depth)
            + "\n"
        )

    data_modules = []
    for start in range(0, len(bucket_items), prefixes_per_module):
        index = start // prefixes_per_module
        data_module = f"Block{index:03d}"
        data_modules.append(data_module)
        (data_directory / f"{data_module}.lean").write_text(lean_module(
            [
                "FourColorTheorem.FourColor.Reducibility."
                "KernelCertificate.OwnerReplay"
            ],
            "\n".join(definitions[start:start + prefixes_per_module]),
        ))

        check_definitions = []
        for prefix, _ in bucket_items[start:start + prefixes_per_module]:
            name = bucket_names[prefix]
            reverse_prefix = "[" + ", ".join(
                gram_symbol(symbol) for symbol in reversed(prefix)
            ) + "]"
            check_definitions.append(f"""
owner_trie_certificate {name}_verified for {reverse_prefix} using {name}
""")
        (check_directory / f"{data_module}.lean").write_text(lean_module(
            [
                "FourColorTheorem.FourColor.Reducibility."
                "KernelCertificate.Config164Segments.Common",
                f"{OWNER_MODULE_ROOT}.{data_module}",
            ],
            "\n".join(check_definitions),
        ))

    prefixes = set(bucket_names)

    def table_expr(prefix: tuple[int, ...]) -> str:
        if not any(candidate[:len(prefix)] == prefix for candidate in prefixes):
            return "OwnerTrie.empty"
        if len(prefix) == prefix_depth:
            return bucket_names[prefix]
        children = [table_expr(prefix + (symbol,)) for symbol in range(4)]
        return "OwnerTrie.node none " + " ".join(
            f"({child})" for child in children
        )

    def sound_expr(prefix: tuple[int, ...]) -> str:
        if not any(candidate[:len(prefix)] == prefix for candidate in prefixes):
            return "OwnerSoundPrefix.empty"
        if len(prefix) == prefix_depth:
            return f"verifyOwnerTrie_sound {bucket_names[prefix]}_verified"
        children = [sound_expr(prefix + (symbol,)) for symbol in range(4)]
        return "OwnerSoundPrefix.node_none " + " ".join(
            f"({child})" for child in children
        )

    table_definition = (
        "def config164OwnerTrie : OwnerTrie :=\n  "
        + table_expr(())
        + "\n\n"
        + "theorem config164OwnerTrie_sound :\n"
        + "    OwnerSound config164Height config164Source "
        + "config164OwnerTrie := by\n"
        + "  unfold OwnerSound config164OwnerTrie\n"
        + "  exact " + sound_expr(()) + "\n\n"
    )
    (data_directory / "Table.lean").write_text(lean_module(
        [f"{OWNER_CHECK_ROOT}.{module}" for module in data_modules],
        table_definition,
    ))

    group_counts = []
    for start in range(0, len(entries), entry_segment_size):
        index = start // entry_segment_size
        group = entries[start:start + entry_segment_size]
        group_counts.append(len(group))
        entry_text = ",\n".join(
            f"  ⟨{code * 6 + tag}⟩" for code, tag, _, _ in group
        )
        body = (
            f"def config164OwnerEntries{index:03d} : List OwnerEntry := [\n"
            + entry_text
            + "\n]"
        )
        (entry_directory / f"Segment{index:03d}.lean").write_text(
            lean_module([
                "FourColorTheorem.FourColor.Reducibility."
                "KernelCertificate.OwnerReplay"
            ], body)
        )
    print(
        f"owners={len(owners)} nonemptyTries={len(buckets)} "
        f"ownerBlocks={len(data_modules)} ownerSegments={len(group_counts)}"
    )
    return group_counts


def write_target_trie(
    directory: pathlib.Path, target_refs: dict[tuple[int, ...], int],
    source_count: int,
    prefixes_per_module: int = 9,
) -> None:
    prefix_depth = 4
    definitions: list[str] = []
    names: dict[tuple[int, ...], str] = {}
    for prefix in product((1, 2, 3), repeat=prefix_depth):
        name = "config164TargetRefs" + "".join(map(str, prefix))
        names[prefix] = name
        suffix_refs = {
            trace[prefix_depth:]: ref
            for trace, ref in target_refs.items()
            if trace[:prefix_depth] == prefix
        }
        definitions.append(
            f"def {name} : RefTrie :=\n  "
            + ref_trie_expr(suffix_refs, HEIGHT - prefix_depth)
            + "\n"
        )

    def top(prefix: tuple[int, ...]) -> str:
        if len(prefix) == prefix_depth:
            return names[prefix]
        return (
            "RefTrie.node none "
            + " ".join(f"({top(prefix + (color,))})" for color in (1, 2, 3))
        )

    modules = []
    module_prefixes: list[list[tuple[int, ...]]] = []
    for start in range(0, len(definitions), prefixes_per_module):
        index = start // prefixes_per_module
        name = f"TargetRefs{index:03d}"
        modules.append(name)
        module_prefixes.append(list(names)[start:start + prefixes_per_module])
        (directory / f"{name}.lean").write_text(lean_module(
            [CORE_IMPORT], "\n".join(definitions[start:start + prefixes_per_module])
        ))
    target_body = "def config164TargetRefs : RefTrie :=\n  " + top(()) + "\n"
    (directory / "Target.lean").write_text(lean_module(
        [f"{MODULE_ROOT}.{name}" for name in modules], target_body
    ))
    return

    check_directory = directory.parent / "Config164TargetChecks"
    check_directory.mkdir(parents=True, exist_ok=True)
    for stale in check_directory.glob("*.lean"):
        stale.unlink()
    color_names = {1: "Color.one", 2: "Color.two", 3: "Color.three"}
    for module, prefixes in zip(modules, module_prefixes, strict=True):
        checks = []
        for prefix in prefixes:
            digits = "".join(map(str, prefix))
            name = names[prefix]
            prefix_text = "[" + ", ".join(color_names[c] for c in prefix) + "]"
            checks.append(f"""
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem config164_target{digits}_verified :
    verifySpecPrefix config164Height config164ContractProgram config164Source
      {source_count} {prefix_text} 8 {name} = true := by
  decide

theorem config164_target{digits}_sound
    (hsound : Config164SourceSound {source_count}) :
    SpecPrefixSound config164Boundary config164ContractProgram
      {prefix_text} 8 :=
  verifySpecPrefix_sound hsound config164_target{digits}_verified
""")
        (check_directory / f"{module}.lean").write_text(lean_module(
            [
                "FourColorTheorem.FourColor.Reducibility."
                "KernelCertificate.Config164Segments.Common",
                f"{MODULE_ROOT}.{module}",
            ],
            "\n".join(checks),
        ))

    sound_alternatives = "\n".join(
        "  | exact config164_target" + "".join(map(str, prefix))
        + "_sound hsound"
        for prefix in names
    )
    all_body = f"""
theorem config164_target_colors_sound
    (hsound : Config164SourceSound {source_count})
    (a b c d : Color)
    (ha : a ≠ Color.zero) (hb : b ≠ Color.zero)
    (hc : c ≠ Color.zero) (hd : d ≠ Color.zero) :
    SpecPrefixSound config164Boundary config164ContractProgram
      [a, b, c, d] 8 := by
  cases a <;> cases b <;> cases c <;> cases d
  all_goals first
  | contradiction
{sound_alternatives}

theorem config164_target_prefix_sound
    (hsound : Config164SourceSound {source_count})
    (path : ColSeq) (hlength : path.length = 4)
    (hnonzero : Color.zero ∉ path) :
    SpecPrefixSound config164Boundary config164ContractProgram path 8 := by
  rcases path with _ | ⟨a, path⟩
  · simp at hlength
  rcases path with _ | ⟨b, path⟩
  · simp at hlength
  rcases path with _ | ⟨c, path⟩
  · simp at hlength
  rcases path with _ | ⟨d, path⟩
  · simp at hlength
  have htail : path = [] := by
    apply List.eq_nil_of_length_eq_zero
    simp only [List.length_cons] at hlength
    omega
  subst path
  simp only [List.mem_cons, List.mem_nil, or_false, not_or] at hnonzero
  exact config164_target_colors_sound hsound a b c d
    hnonzero.1 hnonzero.2.1 hnonzero.2.2.1 hnonzero.2.2.2

theorem config164_contractSpec_sound
    (hsound : Config164SourceSound {source_count}) :
    ∀ et, et.length = config164Height →
      CProg.cpColorSpec config164ContractProgram et →
      Chromogram.KempeCoclosure config164Boundary (ColSeq.ctrace et) := by
  intro et hetLength hspec
  have hlength : et.length = 12 := by
    simpa [config164Height_eq] using hetLength
  let path := et.take 4
  let suffix := et.drop 4
  have hpathLength : path.length = 4 := by
    simp [path, List.length_take]
    omega
  have hsuffixLength : suffix.length = 8 := by
    simp [suffix, List.length_drop]
    omega
  have hnonzero := CProg.cpColorSpec_not_mem_zero hspec
  have hpathNonzero : Color.zero ∉ path := by
    intro hzero
    exact hnonzero (List.mem_of_mem_take hzero)
  have hsuffixNonzero : Color.zero ∉ suffix := by
    intro hzero
    exact hnonzero (List.mem_of_mem_drop hzero)
  have hcovered := config164_target_prefix_sound hsound path
    hpathLength hpathNonzero suffix hsuffixLength hsuffixNonzero
  have hspec' : CProg.cpColorSpec config164ContractProgram
      (path ++ suffix) := by
    simpa [path, suffix] using hspec
  simpa [path, suffix] using hcovered hspec'
"""
    (check_directory / "All.lean").write_text(lean_module(
        [f"{TARGET_CHECK_ROOT}.{module}" for module in modules], all_body
    ))


def cp_step_expr(step) -> str:
    if isinstance(step, tuple):
        return f"(CpStep.rotate {step[1]})"
    return f"CpStep.{step}"


def write_program_stage(
    root: pathlib.Path, index: int, traces: list[tuple[int, ...]],
    refs_per_module: int = 3,
) -> None:
    stage = f"Stage{index:03d}"
    module = f"{PROGRAM_DATA_ROOT}.{stage}"
    directory = root / "Config164ProgramData" / stage
    directory.mkdir(parents=True, exist_ok=True)
    for stale in directory.glob("*.lean"):
        stale.unlink()

    traces = sorted(traces)
    lengths = {len(trace) for trace in traces}
    if len(lengths) != 1:
        raise RuntimeError(f"mixed trace lengths in {stage}: {lengths}")
    length = lengths.pop()
    codes = [encode_trace(trace) for trace in traces]
    source_body = f"""def config164{stage}Count : Nat := {len(traces)}

def config164{stage}Length : Nat := {length}

set_option maxRecDepth 100000 in
def config164{stage}Tree : NatTree :=
  {nat_tree_expr([str(code) for code in codes])}

def config164{stage}Source : SourceTable := config164{stage}Tree.get
"""
    (directory / "Source.lean").write_text(lean_module(
        [CORE_IMPORT], source_body
    ))

    prefix_depth = min(3, length)
    all_refs = {trace: ref for ref, trace in enumerate(traces)}
    buckets: dict[tuple[int, ...], dict[tuple[int, ...], int]] = {}
    for trace, ref in all_refs.items():
        prefix = trace[:prefix_depth]
        buckets.setdefault(prefix, {})[trace[prefix_depth:]] = ref
    names = {
        prefix: f"config164{stage}Refs" + "".join(map(str, prefix))
        for prefix in sorted(buckets)
    }
    definitions = [
        f"set_option maxRecDepth 100000 in\ndef {names[prefix]} : RefTrie :=\n  "
        + ref_trie_expr(buckets[prefix], length - prefix_depth)
        + "\n"
        for prefix in sorted(buckets)
    ]
    refs_modules = []
    prefixes = sorted(buckets)
    for start in range(0, len(definitions), refs_per_module):
        refs_module = f"Refs{start // refs_per_module:03d}"
        refs_modules.append(refs_module)
        (directory / f"{refs_module}.lean").write_text(lean_module(
            [CORE_IMPORT],
            "\n".join(definitions[start:start + refs_per_module]),
        ))

    def top(prefix: tuple[int, ...]) -> str:
        if len(prefix) == prefix_depth:
            return names.get(prefix, "RefTrie.empty")
        children = [top(prefix + (color,)) for color in (1, 2, 3)]
        return "RefTrie.node none " + " ".join(
            f"({child})" for child in children
        )

    refs_body = f"def config164{stage}Refs : RefTrie :=\n  {top(())}\n"
    (directory / "Refs.lean").write_text(lean_module(
        [f"{module}.{name}" for name in refs_modules], refs_body
    ))
    (root / "Config164ProgramData" / f"{stage}.lean").write_text(
        f"import {module}.Source\nimport {module}.Refs\n"
    )


def transition_sound_type(index: int, start: int, count: int) -> str:
    current = f"Stage{index:03d}"
    following = f"Stage{index + 1:03d}"
    return (
        "TransitionRangeSound "
        f"config164{current}Length config164{current}Source "
        f"config164{following}Length config164{following}Source "
        f"config164{following}Count {cp_step_expr(REPLAY_STEPS[index])} "
        f"{start} {count}"
    )


def write_transition_checks(
    root: pathlib.Path, index: int, current_count: int,
    chunk_size: int = 256,
) -> None:
    transition = f"Transition{index:03d}"
    directory = root / "Config164ProgramChecks" / transition
    directory.mkdir(parents=True, exist_ok=True)
    current = f"Stage{index:03d}"
    following = f"Stage{index + 1:03d}"
    chunk_modules = []
    chunks = []
    for start in range(0, current_count, chunk_size):
        count = min(chunk_size, current_count - start)
        chunk_index = start // chunk_size
        chunk = f"Chunk{chunk_index:03d}"
        chunk_modules.append(chunk)
        chunks.append((start, count))
        name = f"config164_transition{index:03d}_{chunk_index:03d}"
        body = f"""config164_transition_certificate {name}_verified and {name}_sound using
  (config164{current}Length, config164{current}Source,
    config164{following}Length, config164{following}Source,
    config164{following}Count, config164{following}Refs,
    {cp_step_expr(REPLAY_STEPS[index])}, {start}, {count})
"""
        (directory / f"{chunk}.lean").write_text(lean_module(
            [
                "FourColorTheorem.FourColor.Reducibility."
                "KernelCertificate.Config164Segments.Common",
                f"{PROGRAM_DATA_ROOT}.{current}",
                f"{PROGRAM_DATA_ROOT}.{following}",
            ],
            body,
        ))

    proof = []
    total = 0
    previous = None
    for chunk_index, (_, count) in enumerate(chunks):
        name = f"config164_transition{index:03d}_{chunk_index:03d}_sound"
        total += count
        aggregate = f"h{chunk_index:03d}"
        if previous is None:
            proof.append(
                f"  have {aggregate} : {transition_sound_type(index, 0, total)} := "
                f"by simpa using {name}"
            )
        else:
            proof.append(
                f"  have {aggregate} : {transition_sound_type(index, 0, total)} := "
                f"by simpa using {previous}.concat {name}"
            )
        previous = aggregate
    proof.append(f"  exact {previous}")
    body = (
        f"theorem config164_transition{index:03d}_sound :\n"
        f"    {transition_sound_type(index, 0, current_count)} := by\n"
        + "\n".join(proof)
        + "\n"
    )
    (root / "Config164ProgramChecks" / f"{transition}.lean").write_text(
        lean_module(
            [f"{PROGRAM_CHECK_ROOT}.{transition}.{chunk}"
             for chunk in chunk_modules],
            body,
        )
    )


def final_sound_type(start: int, count: int) -> str:
    return (
        "FinalRangeSound config164Boundary config164Stage034Length "
        f"config164Stage034Source {start} {count}"
    )


def write_final_checks(
    root: pathlib.Path, source_count: int, final_count: int,
    chunk_size: int = 256,
) -> None:
    directory = root / "Config164ProgramChecks" / "Final"
    directory.mkdir(parents=True, exist_ok=True)
    chunks = []
    imports = []
    for start in range(0, final_count, chunk_size):
        count = min(chunk_size, final_count - start)
        chunk_index = start // chunk_size
        chunk = f"Chunk{chunk_index:03d}"
        imports.append(f"{PROGRAM_CHECK_ROOT}.Final.{chunk}")
        chunks.append((start, count))
        name = f"config164_final_{chunk_index:03d}"
        body = f"""config164_final_certificate {name}_verified and {name}_sound using
  ({source_count}, {start}, {count})
"""
        (directory / f"{chunk}.lean").write_text(lean_module(
            [
                "FourColorTheorem.FourColor.Reducibility."
                "KernelCertificate.Config164Segments.Common",
                f"{PROGRAM_DATA_ROOT}.Stage034",
                f"{MODULE_ROOT}.Target",
            ],
            body,
        ))

    proof = []
    total = 0
    previous = None
    for chunk_index, (_, count) in enumerate(chunks):
        name = f"config164_final_{chunk_index:03d}_sound hsound"
        total += count
        aggregate = f"h{chunk_index:03d}"
        if previous is None:
            proof.append(
                f"  have {aggregate} : {final_sound_type(0, total)} := "
                f"by simpa using {name}"
            )
        else:
            proof.append(
                f"  have {aggregate} : {final_sound_type(0, total)} := "
                f"by simpa using {previous}.concat ({name})"
            )
        previous = aggregate
    proof.append(f"  exact {previous}")
    body = f"""theorem config164_final_sound
    (hsound : Config164SourceSound {source_count}) :
    {final_sound_type(0, final_count)} := by
{chr(10).join(proof)}
"""
    (root / "Config164ProgramChecks" / "Final.lean").write_text(
        lean_module(imports, body)
    )


def write_program_soundness(
    root: pathlib.Path, source_count: int, stage_counts: list[int],
) -> None:
    imports = [
        "FourColorTheorem.FourColor.Reducibility.KernelCertificate."
        "Config164SourceSoundness",
        f"{PROGRAM_DATA_ROOT}.Stage000",
        f"{PROGRAM_CHECK_ROOT}.Final",
    ] + [
        f"{PROGRAM_CHECK_ROOT}.Transition{index:03d}"
        for index in range(len(REPLAY_STEPS))
    ]
    proof = [
        "  have h034 := (config164_final_sound hsound).sourceFoldSound"
    ]
    previous = "h034"
    for index in reversed(range(len(REPLAY_STEPS))):
        current = f"h{index:03d}"
        proof.append(
            f"  have {current} := SourceFoldSound.step "
            f"config164_transition{index:03d}_sound {previous}"
        )
        previous = current
    proof.append(f"  simpa [config164ReplayProgram] using {previous}")
    body = f"""theorem config164_programFold_sound
    (hsound : Config164SourceSound {source_count}) :
    SourceFoldSound (TargetCoclosure config164Boundary)
      config164Stage000Length config164Stage000Source
      config164Stage000Count config164ReplayProgram := by
{chr(10).join(proof)}

theorem config164_contractSpec_sound
    (hsound : Config164SourceSound {source_count})
    {{et : ColSeq}} (hspec : CProg.cpColorSpec config164ContractProgram et) :
    Chromogram.KempeCoclosure config164Boundary (ColSeq.ctrace et) := by
  have hproper : ColSeq.ProperTrace et :=
    ((ColSeq.not_mem_zero_ttail_iff et).1
      (CProg.cpColorSpec_ttail_not_mem_zero hspec)).1
  have hfoldSpec : CProg.cpColorFoldSpec config164ReplayProgram
      [Color.one, Color.two, Color.three] (ColSeq.ttail et) := by
    unfold CProg.cpColorSpec at hspec
    rw [config164_contractProgram_reverse] at hspec
    exact hspec
  have htarget := config164_programFold_sound hsound
    0 21 (by decide) (by decide) (ColSeq.ttail et) hfoldSpec
  exact htarget et hproper rfl
"""
    (root / "Config164ProgramSoundness.lean").write_text(
        lean_module(imports, body)
    )


def write_program_certificate(
    root: pathlib.Path, target_refs: dict[tuple[int, ...], int],
    source_count: int,
) -> None:
    for name in ("Config164ProgramData", "Config164ProgramChecks"):
        directory = root / name
        if directory.exists():
            shutil.rmtree(directory)
        directory.mkdir(parents=True)
    states = [(1, 2, 3)]
    stages = [states]
    for step in REPLAY_STEPS:
        states = sorted(advance_witness_states(
            {trace: (0, 1) for trace in states}, step
        ))
        stages.append(states)
    for index, stage in enumerate(stages):
        write_program_stage(root, index, stage)
    for index, stage in enumerate(stages[:-1]):
        write_transition_checks(root, index, len(stage))
    write_final_checks(root, source_count, len(stages[-1]))
    write_program_soundness(root, source_count, [len(stage) for stage in stages])
    print("program stages=" + ",".join(map(str, map(len, stages))))


def write_lean(
    path: pathlib.Path,
    entries: list[tuple[int, int, list[int], list[int]]],
    source_codes: list[int],
    target_refs: dict[tuple[int, ...], int],
) -> None:
    directory = path.parent / "Config164Data"
    directory.mkdir(parents=True, exist_ok=True)
    for stale in directory.glob("*.lean"):
        stale.unlink()
    base_count = len(source_codes) - len(entries)
    write_source_tree(directory, source_codes, base_count)
    write_target_trie(directory, target_refs, len(source_codes))
    path.write_text(
        f"import {MODULE_ROOT}.Source\n"
        f"import {MODULE_ROOT}.Target\n"
    )


def dependency_closure(
    base_count: int,
    entries: list[tuple[int, int, list[int], list[int]]],
    target_refs: dict[tuple[int, ...], int],
) -> set[int]:
    """Source references needed by the target and their derivations."""
    needed = set(target_refs.values())
    pending = list(needed)
    while pending:
        ref = pending.pop()
        if ref < base_count:
            continue
        entry_index = ref - base_count
        if entry_index >= len(entries):
            raise RuntimeError(f"invalid derived source reference {ref}")
        for support_ref in entries[entry_index][2]:
            if support_ref >= ref:
                raise RuntimeError(
                    f"non-topological support {support_ref} for source {ref}"
                )
            if support_ref not in needed:
                needed.add(support_ref)
                pending.append(support_ref)
    return needed


def prune_certificate(
    base_codes: list[int],
    entries: list[tuple[int, int, list[int], list[int]]],
    target_refs: dict[tuple[int, ...], int],
    needed_refs: set[int],
) -> tuple[
    list[tuple[int, int, list[int], list[int]]],
    list[int],
    dict[tuple[int, ...], int],
]:
    """Retain the dependency closure and densely remap source references."""
    base_count = len(base_codes)
    ref_map = {ref: ref for ref in range(base_count)}
    selected_entries = []
    selected_codes = []
    for entry_index, (code, tag, support, selectors) in enumerate(entries):
        old_ref = base_count + entry_index
        if old_ref not in needed_refs:
            continue
        missing = [ref for ref in support if ref not in ref_map]
        if missing:
            raise RuntimeError(
                f"missing remapped supports {missing} for source {old_ref}"
            )
        new_ref = base_count + len(selected_entries)
        ref_map[old_ref] = new_ref
        selected_entries.append(
            (code, tag, [ref_map[ref] for ref in support], selectors)
        )
        selected_codes.append(code)
    remapped_targets = {
        trace: ref_map[ref] for trace, ref in target_refs.items()
    }
    return selected_entries, base_codes + selected_codes, remapped_targets


def write_segments(
    path: pathlib.Path, base_witnesses: list[int], group_counts: list[int],
    base_chunk_size: int = 128,
) -> None:
    path.mkdir(parents=True, exist_ok=True)
    for pattern in ("Base*.lean", "Segment*.lean"):
        for stale in path.glob(pattern):
            stale.unlink()
    base_count = len(base_witnesses)
    start = 0
    for index in range((base_count + base_chunk_size - 1) // base_chunk_size):
        witnesses = base_witnesses[start:start + base_chunk_size]
        count = len(witnesses)
        finish = start + count
        witness_text = ",\n    ".join(str(witness) for witness in witnesses)
        source = f"""import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164Segments.Common

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

def config164BaseWitnesses{index:03d} : List Nat := [
    {witness_text}
]

config164_base_certificate config164_base{index:03d}_verified and
  config164_base{index:03d}_sound using config164BaseWitnesses{index:03d}
  from {start} to {finish}

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
"""
        (path / f"Base{index:03d}.lean").write_text(source)
        start = finish
    if start != base_count:
        raise RuntimeError("base range partition has the wrong size")

    start = base_count
    for index, count in enumerate(group_counts):
        finish = start + count
        source = f"""import FourColorTheorem.FourColor.Reducibility.KernelCertificate.Config164Segments.Common
import {OWNER_MODULE_ROOT}.Table
import {OWNER_ENTRY_ROOT}.Segment{index:03d}

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

config164_owner_segment_certificate config164_segment{index:03d}_verified and
  config164_segment{index:03d}_sound using config164OwnerEntries{index:03d}
  from {start} to {finish}

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
"""
        (path / f"Segment{index:03d}.lean").write_text(source)
        start = finish

    imports = [
        f"FourColorTheorem.FourColor.Reducibility.KernelCertificate."
        f"Config164Segments.Base{index:03d}"
        for index in range((base_count + base_chunk_size - 1) // base_chunk_size)
    ] + [
        f"FourColorTheorem.FourColor.Reducibility.KernelCertificate."
        f"Config164Segments.Segment{index:03d}"
        for index in range(len(group_counts))
    ]
    proof_lines = []
    previous = "config164_sourceSound_zero"
    for index in range((base_count + base_chunk_size - 1) // base_chunk_size):
        current = f"hbase{index:03d}"
        proof_lines.append(
            f"  have {current} := config164_base{index:03d}_sound {previous}"
        )
        previous = current
    for index in range(len(group_counts)):
        current = f"hsegment{index:03d}"
        proof_lines.append(
            f"  have {current} := config164_segment{index:03d}_sound {previous}"
        )
        previous = current
    proof_lines.append(f"  exact {previous}")
    body = (
        f"theorem config164_source_sound : Config164SourceSound {start} := by\n"
        + "\n".join(proof_lines)
        + "\n"
    )
    (path.parent / "Config164SourceSoundness.lean").write_text(
        lean_module(imports, body)
    )


def main() -> None:
    root = pathlib.Path("/tmp")
    base = read_codes(root / "kernelcert164-base.txt")
    target = read_codes(root / "kernelcert164-target.txt")
    hit_words: dict[int, int] = {}
    start = time.monotonic()
    base_codes = sorted(base, key=decode_trace)
    source_codes = list(base_codes)
    code_refs = {code: ref for ref, code in enumerate(base_codes)}
    for code, ref in code_refs.items():
        add_hits(decode_trace(code), hit_words, ref)
    print(f"base={len(base)} target={len(target)} hitWords={len(hit_words)}")

    valid = []
    for code in range(3 ** HEIGHT):
        trace = decode_trace(code)
        if valid_trace(trace) and code not in base:
            valid.append(code)
    print(f"valid={len(valid) + len(base)} candidates={len(valid)}")

    known = set(base)
    entries: list[tuple[int, int, list[int], list[int]]] = []
    remaining = valid
    round_number = 0
    while not target <= known:
        pass_start = time.monotonic()
        next_remaining = []
        added = 0
        for code in remaining:
            trace = decode_trace(code)
            derivation = find_permutation(trace, hit_words)
            if derivation is None:
                next_remaining.append(code)
                continue
            tag, witnesses = derivation
            support = [code for code, _ in Counter(witnesses).most_common()]
            support_index = {owner: index for index, owner in enumerate(support)}
            selectors = [support_index[owner] for owner in witnesses]
            known.add(code)
            entries.append((code, tag, support, selectors))
            ref = len(source_codes)
            source_codes.append(code)
            code_refs[code] = ref
            add_hits(trace, hit_words, ref)
            added += 1
        print(
            f"pass={round_number} added={added} remaining={len(next_remaining)} "
            f"entries={len(entries)} hitWords={len(hit_words)} "
            f"seconds={time.monotonic() - pass_start:.2f}",
            flush=True,
        )
        if added == 0:
            missing = target - known
            raise RuntimeError(f"closure stalled with {len(missing)} target traces missing")
        remaining = next_remaining
        round_number += 1

    target_refs = {decode_trace(code): code_refs[code] for code in target}
    needed_refs = dependency_closure(len(base_codes), entries, target_refs)
    needed_derived = sum(ref >= len(base_codes) for ref in needed_refs)
    print(
        f"target dependency closure: {needed_derived} derived entries, "
        f"{len(needed_refs) - needed_derived} base entries",
        flush=True,
    )
    if "--analyze" in sys.argv[1:]:
        return

    entries, source_codes, target_refs = prune_certificate(
        base_codes, entries, target_refs, needed_refs
    )

    output = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else pathlib.Path(
        "FourColorTheorem/FourColor/Reducibility/KernelCertificate/Config164IndexedData.lean"
    )
    if "--target-only" in sys.argv[1:]:
        directory = output.parent / "Config164Data"
        write_target_trie(directory, target_refs, len(source_codes))
        print(f"wrote target certificate for {len(target_refs)} traces")
        return
    write_lean(output, entries, source_codes, target_refs)
    group_counts = write_owner_certificate(
        output.parent, entries, source_codes
    )
    base_witnesses = configuration164_base_witnesses(base_codes)
    write_segments(
        output.parent / "Config164Segments", base_witnesses, group_counts
    )
    write_program_certificate(output.parent, target_refs, len(source_codes))
    support_count = sum(len(support) for _, _, support, _ in entries)
    selector_count = sum(len(selectors) for _, _, _, selectors in entries)
    max_support = max(map(len, (support for _, _, support, _ in entries)))
    print(
        f"covered target with {len(entries)} derived entries and "
        f"{support_count} support references (max {max_support}) plus "
        f"{selector_count} selectors in "
        f"{time.monotonic() - start:.2f}s; wrote {output}",
        flush=True,
    )


if __name__ == "__main__":
    main()
