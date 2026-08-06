import FourColorTheorem.FourColor.Coloring.Birkhoff.DiskInterior

/-! Ring-adjacency geometry around a cubic hub. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

open PointedHypermap

namespace Birkhoff

universe u

/-- Coq `birkhoff.v::fband_spoke_ring`: the face band of the spoke ring is
exactly the set of faces adjacent to its hub. -/
theorem faceBand_spokeRing_iff_ringAdj
    {G : Hypermap.{u}} (x y : G.Dart) :
    G.FaceBand (spokeRing G x) y ↔ G.RingAdj x y := by
  constructor
  · rintro ⟨z, hzRing, hzy⟩
    refine ⟨G.node z, ?_, ?_⟩
    · exact (mem_spokeRing_iff G x z).mp hzRing
    · rw [Hypermap.edge_node_eq_face_symm]
      exact PermReachable.trans G.face
        (by simpa using PermReachable.forward G.face (G.face.symm z)) hzy
  · rintro ⟨z, hxz, hedgeZY⟩
    refine ⟨spoke G z, ?_, ?_⟩
    · rw [mem_spokeRing_iff]
      simpa [spoke] using hxz
    · exact PermReachable.trans G.face
        (by simpa [spoke] using
          PermReachable.backward G.face (spoke G z)) hedgeZY

/-- Coq `birkhoff.v::adj11_edge`: if a face and its opposite face are both
adjacent to one hub, one of their darts lies on the hub's spoke ring. -/
theorem ringAdj_or_edge_mem_spokeRing
    {G : Hypermap.{u}}
    (hG : G.MinimalCounterexample) (hconnected : G.Connected)
    (hcubic : G.Cubic) (x y : G.Dart)
    (hy : G.RingAdj x y) (hey : G.RingAdj x (G.edge y)) :
    y ∈ spokeRing G x ∨ G.edge y ∈ spokeRing G x := by
  by_contra hneither
  push Not at hneither
  rcases hneither with ⟨hyOff, heyOff⟩
  rcases (faceBand_spokeRing_iff_ringAdj x y).2 hy with
    ⟨z, hzRing, hzy⟩
  rcases (faceBand_spokeRing_iff_ringAdj x (G.edge y)).2 hey with
    ⟨t, htRing, htey⟩
  have hzt : G.RingAdj z t := by
    refine ⟨y, hzy, ?_⟩
    exact PermReachable.symm G.face htey
  rcases chordless_spokeRing hG hconnected hcubic x z hzRing t htRing hzt with
    htPrev | htNext
  · have hzNext : z = (spokeRing G x).next t htRing := by
      simpa [htPrev] using
        (List.next_prev (spokeRing G x) (spokeRing_nodup G x) z hzRing).symm
    have hedgeTY : PermReachable G.face (G.edge t) y := by
      have hedgeTZ : PermReachable G.face (G.edge t) z := by
        rw [hzNext, next_spokeRing hG.plain hcubic x t htRing]
        exact PermReachable.trans G.face
          (PermReachable.forward G.face (G.edge t))
          (PermReachable.forward G.face (spoke G t))
      exact PermReachable.trans G.face hedgeTZ hzy
    have hedgeYEqT : G.edge y = t :=
      doubleDart hG hconnected hcubic
        (PermReachable.symm G.face htey)
        (by
          simpa [Hypermap.Plain.edge_edge (G := G) hG.plain y] using
            PermReachable.symm G.face hedgeTY)
    exact heyOff (by simpa [hedgeYEqT] using htRing)
  · have htFaceEdgeZ :
      PermReachable G.face (G.edge z) t := by
      rw [htNext, next_spokeRing hG.plain hcubic x z hzRing]
      exact PermReachable.trans G.face
        (PermReachable.forward G.face (G.edge z))
        (PermReachable.forward G.face (spoke G z))
    have hyEqZ : y = z :=
      doubleDart hG hconnected hcubic
        (PermReachable.symm G.face hzy)
        (PermReachable.trans G.face
          (PermReachable.symm G.face htey)
          (PermReachable.symm G.face htFaceEdgeZ))
    exact hyOff (by simpa [hyEqZ] using hzRing)

/-- Coq `birkhoff.v::adj12_edge`.  If two faces adjacent to a hub are
arranged across a third adjacency, one of the two possible closing
adjacencies is present. -/
theorem ringAdj_or_faceReachable_of_ringAdj_edge
    {G : Hypermap.{u}}
    (hG : G.MinimalCounterexample) (hconnected : G.Connected)
    (hcubic : G.Cubic) (x y z : G.Dart)
    (hxy : G.RingAdj x y) (hxz : G.RingAdj x z)
    (hzey : G.RingAdj z (G.edge y)) :
    (PermReachable G.face z y ∨ G.RingAdj z y) ∨
      (PermReachable G.face x (G.edge y) ∨
        G.RingAdj x (G.edge y)) := by
  classical
  by_contra hclose
  push Not at hclose
  rcases hclose with ⟨⟨hzNotFaceY, hzNotAdjY⟩,
    hxNotFaceEdgeY, hxNotAdjEdgeY⟩
  rcases (faceBand_spokeRing_iff_ringAdj x y).2 hxy with
    ⟨y₁, hy₁Ring, hy₁y⟩
  rcases (faceBand_spokeRing_iff_ringAdj x z).2 hxz with
    ⟨z₁, hz₁Ring, hz₁z⟩
  rcases hzey with ⟨x₁, hzx₁, hedgeX₁EdgeY⟩
  have hxNodeY₁ : PermReachable G.face x (G.node y₁) :=
    (mem_spokeRing_iff G x y₁).mp hy₁Ring
  have hxNodeZ₁ : PermReachable G.face x (G.node z₁) :=
    (mem_spokeRing_iff G x z₁).mp hz₁Ring
  let a := y
  let b := G.edge x₁
  let c := G.edge (G.node z₁)
  let d := G.node y₁
  let q : List G.Dart := [a, b, c, d]
  have hcZ₁ : PermReachable G.face c z₁ := by
    dsimp [c]
    rw [Hypermap.edge_node_eq_face_symm]
    simpa using PermReachable.forward G.face (G.face.symm z₁)
  have hab : G.RLink a b := by
    dsimp [a, b]
    unfold Hypermap.RLink
    exact PermReachable.symm G.face hedgeX₁EdgeY
  have hbc : G.RLink b c := by
    dsimp [b, c]
    unfold Hypermap.RLink
    rw [Hypermap.Plain.edge_edge (G := G) hG.plain x₁,
      Hypermap.edge_node_eq_face_symm]
    exact PermReachable.trans G.face
      (PermReachable.symm G.face
        (PermReachable.trans G.face hz₁z hzx₁))
      (PermReachable.backward G.face z₁)
  have hcd : G.RLink c d := by
    dsimp [c, d]
    unfold Hypermap.RLink
    rw [Hypermap.Plain.edge_edge (G := G) hG.plain (G.node z₁)]
    exact PermReachable.trans G.face
      (PermReachable.symm G.face hxNodeZ₁) hxNodeY₁
  have hda : G.RLink d a := by
    dsimp [d, a]
    unfold Hypermap.RLink
    rw [Hypermap.edge_node_eq_face_symm]
    exact PermReachable.trans G.face
      (by simpa using PermReachable.forward G.face (G.face.symm y₁)) hy₁y
  have hAB : ¬ PermReachable G.face a b := by
    dsimp [a, b]
    intro hyEdgeX₁
    exact hG.bridgeless y
      (PermReachable.trans G.face hyEdgeX₁ hedgeX₁EdgeY)
  have hAC : ¬ PermReachable G.face a c := by
    dsimp [a, c]
    intro hyc
    apply hzNotFaceY
    exact PermReachable.symm G.face
      (PermReachable.trans G.face hyc
        (PermReachable.trans G.face hcZ₁ hz₁z))
  have hAD : ¬ PermReachable G.face a d := by
    dsimp [a, d]
    intro hyd
    exact Hypermap.Bridgeless.not_faceReachable_node
      (G := G) hG.bridgeless y₁
      (PermReachable.trans G.face hy₁y hyd)
  have hBC : ¬ PermReachable G.face b c := by
    dsimp [b, c]
    intro hbcFace
    apply hG.bridgeless x₁
    exact PermReachable.symm G.face
      (PermReachable.trans G.face hbcFace
        (PermReachable.trans G.face hcZ₁
          (PermReachable.trans G.face hz₁z hzx₁)))
  have hBD : ¬ PermReachable G.face b d := by
    dsimp [b, d]
    intro hbd
    apply hxNotFaceEdgeY
    exact PermReachable.trans G.face hxNodeY₁
      (PermReachable.trans G.face
        (PermReachable.symm G.face hbd) hedgeX₁EdgeY)
  have hCD : ¬ PermReachable G.face c d := by
    dsimp [c, d]
    intro hcdFace
    apply hzNotAdjY
    refine ⟨G.node y₁, ?_, ?_⟩
    · exact PermReachable.trans G.face
        (PermReachable.symm G.face hz₁z)
        (PermReachable.trans G.face
          (PermReachable.symm G.face hcZ₁) hcdFace)
    · rw [Hypermap.edge_node_eq_face_symm]
      exact PermReachable.trans G.face
        (by simpa using PermReachable.forward G.face (G.face.symm y₁)) hy₁y
  have hq : G.SimpleRLinkCycle q := by
    constructor
    · exact ⟨⟨hab, ⟨hbc, ⟨hcd, by simp⟩⟩⟩, hda⟩
    · simp [q, Hypermap.FaceSimple, hAB, hAC, hAD, hBC, hBD, hCD]
  let u := G.node (G.node y₁)
  let v := G.node (G.node z₁)
  have hy₁u : PermReachable G.face (G.edge y₁) u := by
    dsimp [u]
    rw [Hypermap.Cubic.node_node_eq_face_edge (G := G) hcubic y₁]
    exact PermReachable.forward G.face (G.edge y₁)
  have hz₁v : PermReachable G.face (G.edge z₁) v := by
    dsimp [v]
    rw [Hypermap.Cubic.node_node_eq_face_edge (G := G) hcubic z₁]
    exact PermReachable.forward G.face (G.edge z₁)
  have hyAdjU : G.RingAdj y u :=
    Hypermap.RingAdj.of_faceReachable_right (G := G)
      (Hypermap.RingAdj.of_faceReachable_left (G := G)
        (PermReachable.symm G.face hy₁y)
        (Hypermap.RingAdj.edge_self (G := G) y₁)) hy₁u
  have hzAdjV : G.RingAdj z v :=
    Hypermap.RingAdj.of_faceReachable_right (G := G)
      (Hypermap.RingAdj.of_faceReachable_left (G := G)
        (PermReachable.symm G.face hz₁z)
        (Hypermap.RingAdj.edge_self (G := G) z₁)) hz₁v
  have hxAdjU : G.RingAdj x u := by
    have hlocal : G.RingAdj (G.node y₁) u := by
      simpa [u] using Hypermap.RingAdj.symm_of_plain (G := G) hG.plain
        (Hypermap.RingAdj.node_self (G := G) (G.node y₁))
    exact Hypermap.RingAdj.of_faceReachable_left (G := G)
      hxNodeY₁ hlocal
  have hxAdjV : G.RingAdj x v := by
    have hlocal : G.RingAdj (G.node z₁) v := by
      simpa [v] using Hypermap.RingAdj.symm_of_plain (G := G) hG.plain
        (Hypermap.RingAdj.node_self (G := G) (G.node z₁))
    exact Hypermap.RingAdj.of_faceReachable_left (G := G)
      hxNodeZ₁ hlocal
  have hyNotAdjZ : ¬ G.RingAdj y z := by
    intro hyz
    exact hzNotAdjY
      (Hypermap.RingAdj.symm_of_plain (G := G) hG.plain hyz)
  have huDisk : G.DiskN q u := by
    have hdDisk : G.DiskN q d := G.diskN_of_mem (by simp [q])
    have hnodeD : G.DiskN q (G.node d) :=
      (G.diskN_node_iff (r := q)).2 hdDisk
    simpa [d, u] using hnodeD
  have huBand : ¬ G.FaceBand q u := by
    rintro ⟨s, hs, hsu⟩
    simp only [q, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with hs | hs | hs | hs
    · subst s
      exact Hypermap.Bridgeless.not_faceReachable_of_ringAdj
        (G := G) hG.bridgeless hyAdjU hsu
    · subst s
      exact (Hypermap.RingAdj.not_faceReachable_of_not_ringAdj_of_ringAdj
        (G := G) hxNotAdjEdgeY hxAdjU)
        (PermReachable.trans G.face
          (PermReachable.symm G.face hedgeX₁EdgeY) hsu)
    · subst s
      have hzu : ¬ PermReachable G.face z u :=
        Hypermap.RingAdj.not_faceReachable_of_not_ringAdj_of_ringAdj
          (G := G) hyNotAdjZ hyAdjU
      apply hzu
      exact PermReachable.trans G.face
        (PermReachable.symm G.face hz₁z)
        (PermReachable.trans G.face
          (PermReachable.symm G.face hcZ₁) hsu)
    · subst s
      exact Hypermap.Bridgeless.not_faceReachable_of_ringAdj
        (G := G) hG.bridgeless
        (Hypermap.RingAdj.symm_of_plain (G := G) hG.plain
          (Hypermap.RingAdj.node_self (G := G) (G.node y₁))) hsu
  have hvDisk : ¬ G.DiskN q v := by
    intro hv
    have hzNodeDisk : G.DiskN q (G.node z₁) :=
      (G.diskN_node_iff (r := q)).1 (by simpa [v] using hv)
    have hproper : G.ProperRing q :=
      Hypermap.properRing_of_length_gt_two (G := G) (by simp [q])
    have hJordan : G.Jordan :=
      Unavoidability.eulerPlanar_jordan G hG.planar
    have hnot := G.diskN_edge_ring hJordan hG.plain hq hproper
      (x := c) (by simp [q])
    apply hnot
    simpa [c, Hypermap.Plain.edge_edge (G := G) hG.plain] using hzNodeDisk
  have hvBand : ¬ G.FaceBand q v := by
    rintro ⟨s, hs, hsv⟩
    simp only [q, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with hs | hs | hs | hs
    · subst s
      exact (Hypermap.RingAdj.not_faceReachable_of_not_ringAdj_of_ringAdj
        (G := G) hzNotAdjY hzAdjV) hsv
    · subst s
      exact (Hypermap.RingAdj.not_faceReachable_of_not_ringAdj_of_ringAdj
        (G := G) hxNotAdjEdgeY hxAdjV)
        (PermReachable.trans G.face
          (PermReachable.symm G.face hedgeX₁EdgeY) hsv)
    · subst s
      have hz₁AdjV : G.RingAdj z₁ v :=
        Hypermap.RingAdj.of_faceReachable_right (G := G)
          (Hypermap.RingAdj.edge_self (G := G) z₁) hz₁v
      exact Hypermap.Bridgeless.not_faceReachable_of_ringAdj
        (G := G) hG.bridgeless hz₁AdjV
        (PermReachable.trans G.face
          (PermReachable.symm G.face hcZ₁) hsv)
    · subst s
      exact Hypermap.Bridgeless.not_faceReachable_node
        (G := G) hG.bridgeless (G.node z₁)
        (PermReachable.trans G.face
          (PermReachable.symm G.face hxNodeZ₁)
          (PermReachable.trans G.face hxNodeY₁ hsv))
  have hnt : G.NontrivialRing 0 q :=
    (Hypermap.nontrivialRing_zero_iff (G := G)).2
      ⟨⟨u, huDisk, huBand⟩, ⟨v, hvDisk, hvBand⟩⟩
  exact (Birkhoff hG hconnected hcubic q (by simp [q]) hq) hnt

private theorem prev_prev_ne_next_of_four_lt_length
    {α : Type*} [DecidableEq α] (r : List α) (hr : r.Nodup)
    (hlen : 4 < r.length) (x : α) (hx : x ∈ r) :
    r.prev (r.prev x hx) (List.prev_mem r x hx) ≠ r.next x hx := by
  intro hbad
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  let j := (i + (r.length - 1)) % r.length
  have hj : j < r.length := Nat.mod_lt _ (by omega)
  let k := (j + (r.length - 1)) % r.length
  have hk : k < r.length := Nat.mod_lt _ (by omega)
  let n := (i + 1) % r.length
  have hn : n < r.length := Nat.mod_lt _ (by omega)
  have hprev : r.prev r[i] hx = r[j] := by
    simpa [j] using List.prev_getElem r hr i hi
  have hprevPrev :
      r.prev (r.prev r[i] hx) (List.prev_mem r r[i] hx) = r[k] := by
    simpa only [hprev] using List.prev_getElem r hr j hj
  have hnext : r.next r[i] hx = r[n] := by
    simpa [n] using List.next_getElem r hr i hi
  have hindex : k = n :=
    hr.getElem_inj_iff.mp (hprevPrev.symm.trans (hbad.trans hnext))
  let N := r.length
  let A := i + 2 * (N - 1)
  let B := i + 1
  have hkA : k = A % N := by
    dsimp [k, j, A, N]
    rw [show i + 2 * (r.length - 1) =
        (i + (r.length - 1)) + (r.length - 1) by omega]
    exact Nat.mod_add_mod (i + (r.length - 1)) r.length
      (r.length - 1)
  have hnB : n = B % N := by rfl
  have hmod : A % N = B % N := by
    rw [← hkA, ← hnB]
    exact hindex
  have hBA : B ≤ A := by dsimp [A, B, N]; omega
  have hquotientLe : B - B % N ≤ A - A % N := by omega
  have hdivA : N ∣ A - A % N := Nat.dvd_sub_mod A
  have hdivB : N ∣ B - B % N := Nat.dvd_sub_mod B
  have hdivDiff : N ∣ (A - A % N) - (B - B % N) :=
    Nat.dvd_sub hdivA hdivB
  have hdiff : (A - A % N) - (B - B % N) = 2 * N - 3 := by
    rw [hmod]
    rw [Nat.sub_sub_sub_cancel_right (Nat.mod_le B N)]
    dsimp [A, B, N]
    omega
  have hdivAlmost : N ∣ 2 * N - 3 := by simpa [hdiff] using hdivDiff
  have hdivThree : N ∣ 3 := by
    have hdivTwoN : N ∣ 2 * N := Nat.dvd_mul_left N 2
    have : N ∣ 2 * N - (2 * N - 3) :=
      Nat.dvd_sub hdivTwoN hdivAlmost
    convert this using 1
    all_goals omega
  have hNleThree : N ≤ 3 := Nat.le_of_dvd (by omega) hdivThree
  dsimp [N] at hNleThree
  omega

/-- Direct three-witness form of Coq `birkhoff.v::fcard_adj_max`: two
distinct face orbits in a minimal counterexample cannot have three pairwise
distinct common adjacent face orbits. -/
theorem not_three_common_ringAdj
    {G : Hypermap.{u}}
    (hG : G.MinimalCounterexample) (hconnected : G.Connected)
    (hcubic : G.Cubic) {x y a b c : G.Dart}
    (hminArity : 5 ≤ G.arity x)
    (hxyFace : ¬ PermReachable G.face x y)
    (hab : ¬ PermReachable G.face a b)
    (hac : ¬ PermReachable G.face a c)
    (hbc : ¬ PermReachable G.face b c)
    (hxa : G.RingAdj x a) (hxb : G.RingAdj x b)
    (hxc : G.RingAdj x c) (hya : G.RingAdj y a)
    (hyb : G.RingAdj y b) (hyc : G.RingAdj y c) : False := by
  classical
  let r := spokeRing G x
  have hr : G.SimpleRLinkCycle r := by
    simpa [r] using spokeRing_simpleRLinkCycle hG hconnected hcubic x
  have hrNodup : r.Nodup := hr.faceSimple.nodup
  have hrLength : 4 < r.length := by
    change 4 < (spokeRing G x).length
    rw [length_spokeRing]
    exact hminArity
  rcases (faceBand_spokeRing_iff_ringAdj x a).2 hxa with
    ⟨a₁, ha₁r, ha₁a⟩
  rcases (faceBand_spokeRing_iff_ringAdj x b).2 hxb with
    ⟨b₁, hb₁r, hb₁b⟩
  rcases (faceBand_spokeRing_iff_ringAdj x c).2 hxc with
    ⟨c₁, hc₁r, hc₁c⟩
  have ha₁r' : a₁ ∈ r := by simpa [r] using ha₁r
  have hb₁r' : b₁ ∈ r := by simpa [r] using hb₁r
  have hc₁r' : c₁ ∈ r := by simpa [r] using hc₁r
  have distinctLifts
      {s t s₁ t₁ : G.Dart}
      (hs₁s : PermReachable G.face s₁ s)
      (ht₁t : PermReachable G.face t₁ t)
      (hst : ¬ PermReachable G.face s t) : s₁ ≠ t₁ := by
    intro heq
    apply hst
    exact PermReachable.trans G.face
      (PermReachable.symm G.face hs₁s) (by simpa [heq] using ht₁t)
  have ha₁neB₁ : a₁ ≠ b₁ := distinctLifts ha₁a hb₁b hab
  have ha₁neC₁ : a₁ ≠ c₁ := distinctLifts ha₁a hc₁c hac
  have hb₁neC₁ : b₁ ≠ c₁ := distinctLifts hb₁b hc₁c hbc
  have transportAdj
      {s t s₁ t₁ : G.Dart}
      (hs₁s : PermReachable G.face s₁ s)
      (htt₁ : PermReachable G.face t t₁)
      (hst : G.RingAdj s t) : G.RingAdj s₁ t₁ :=
    Hypermap.RingAdj.of_faceReachable_right (G := G)
      (Hypermap.RingAdj.of_faceReachable_left (G := G) hs₁s hst) htt₁
  have hchordless := chordless_spokeRing hG hconnected hcubic x
  by_cases hxyAdj : G.RingAdj x y
  · rcases (faceBand_spokeRing_iff_ringAdj x y).2 hxyAdj with
      ⟨y₁, hy₁r, hy₁y⟩
    have hya₁ : G.RingAdj y₁ a₁ :=
      transportAdj hy₁y (PermReachable.symm G.face ha₁a) hya
    have hyb₁ : G.RingAdj y₁ b₁ :=
      transportAdj hy₁y (PermReachable.symm G.face hb₁b) hyb
    have hyc₁ : G.RingAdj y₁ c₁ :=
      transportAdj hy₁y (PermReachable.symm G.face hc₁c) hyc
    have hy₁r' : y₁ ∈ r := by simpa [r] using hy₁r
    have haNear := hchordless y₁ hy₁r' a₁ ha₁r' hya₁
    have hbNear := hchordless y₁ hy₁r' b₁ hb₁r' hyb₁
    have hcNear := hchordless y₁ hy₁r' c₁ hc₁r' hyc₁
    rcases haNear with haPrev | haNext <;>
      rcases hbNear with hbPrev | hbNext <;>
      rcases hcNear with hcPrev | hcNext
    all_goals first
      | exact ha₁neB₁ (haPrev.trans hbPrev.symm)
      | exact ha₁neB₁ (haNext.trans hbNext.symm)
      | exact ha₁neC₁ (haPrev.trans hcPrev.symm)
      | exact ha₁neC₁ (haNext.trans hcNext.symm)
      | exact hb₁neC₁ (hbPrev.trans hcPrev.symm)
      | exact hb₁neC₁ (hbNext.trans hcNext.symm)
  · have crossAdj
        {s t : G.Dart}
        (hstFace : ¬ PermReachable G.face s t)
        (hxs : G.RingAdj x s) (hxt : G.RingAdj x t)
        (hys : G.RingAdj y s) (hyt : G.RingAdj y t) :
        G.RingAdj s t := by
      rcases hyt with ⟨u, hyu, hedgeUT⟩
      have hxEdgeU : G.RingAdj x (G.edge u) :=
        Hypermap.RingAdj.of_faceReachable_right (G := G) hxt
          (PermReachable.symm G.face hedgeUT)
      have hsEdgeEdgeU : G.RingAdj s (G.edge (G.edge u)) := by
        have huS : G.RingAdj u s :=
          (Hypermap.RingAdj.congr_faceReachable_left (G := G) hyu).1 hys
        have hsU : G.RingAdj s u :=
          Hypermap.RingAdj.symm_of_plain (G := G) hG.plain huS
        simpa [Hypermap.Plain.edge_edge (G := G) hG.plain] using hsU
      rcases ringAdj_or_faceReachable_of_ringAdj_edge
          hG hconnected hcubic x (G.edge u) s hxEdgeU hxs hsEdgeEdgeU with
        (hsFaceEdgeU | hsAdjEdgeU) | hxClose
      · exact False.elim (hstFace
          (PermReachable.trans G.face hsFaceEdgeU hedgeUT))
      · exact Hypermap.RingAdj.of_faceReachable_right (G := G)
          hsAdjEdgeU hedgeUT
      · rcases hxClose with hxFaceEdgeEdgeU | hxAdjEdgeEdgeU
        · apply False.elim
          apply hxyFace
          have hxU : PermReachable G.face x u := by
            simpa [Hypermap.Plain.edge_edge (G := G) hG.plain] using
              hxFaceEdgeEdgeU
          exact PermReachable.trans G.face hxU
            (PermReachable.symm G.face hyu)
        · apply False.elim
          apply hxyAdj
          have hxU : G.RingAdj x u := by
            simpa [Hypermap.Plain.edge_edge (G := G) hG.plain] using
              hxAdjEdgeEdgeU
          exact Hypermap.RingAdj.of_faceReachable_right (G := G) hxU
            (PermReachable.symm G.face hyu)
    have habAdj : G.RingAdj a b := crossAdj hab hxa hxb hya hyb
    have hacAdj : G.RingAdj a c := crossAdj hac hxa hxc hya hyc
    have hbcAdj : G.RingAdj b c := crossAdj hbc hxb hxc hyb hyc
    have hcbAdj : G.RingAdj c b :=
      Hypermap.RingAdj.symm_of_plain (G := G) hG.plain hbcAdj
    have ha₁b₁ : G.RingAdj a₁ b₁ :=
      transportAdj ha₁a (PermReachable.symm G.face hb₁b) habAdj
    have ha₁c₁ : G.RingAdj a₁ c₁ :=
      transportAdj ha₁a (PermReachable.symm G.face hc₁c) hacAdj
    have hb₁c₁ : G.RingAdj b₁ c₁ :=
      transportAdj hb₁b (PermReachable.symm G.face hc₁c) hbcAdj
    have hc₁b₁ : G.RingAdj c₁ b₁ :=
      transportAdj hc₁c (PermReachable.symm G.face hb₁b) hcbAdj
    have hbNear := hchordless a₁ ha₁r' b₁ hb₁r' ha₁b₁
    have hcNear := hchordless a₁ ha₁r' c₁ hc₁r' ha₁c₁
    rcases hbNear with hbPrev | hbNext
    · rcases hcNear with hcPrev | hcNext
      · exact hb₁neC₁ (hbPrev.trans hcPrev.symm)
      · have hbcNear := hchordless b₁ hb₁r' c₁ hc₁r' hb₁c₁
        rcases hbcNear with hcbPrev | hcbNext
        · exact prev_prev_ne_next_of_four_lt_length r hrNodup hrLength
            a₁ ha₁r'
            (by simpa [hbPrev, hcNext] using hcbPrev.symm)
        · exact ha₁neC₁ (by
            calc
              a₁ = r.next (r.prev a₁ ha₁r')
                  (List.prev_mem r a₁ ha₁r') :=
                (List.next_prev r hrNodup a₁ ha₁r').symm
              _ = c₁ := by simpa [hbPrev] using hcbNext.symm)
    · rcases hcNear with hcPrev | hcNext
      · have hcbNear := hchordless c₁ hc₁r' b₁ hb₁r' hc₁b₁
        rcases hcbNear with hbcPrev | hbcNext
        · exact prev_prev_ne_next_of_four_lt_length r hrNodup hrLength
            a₁ ha₁r'
            (by simpa [hcPrev, hbNext] using hbcPrev.symm)
        · exact ha₁neB₁ (by
            calc
              a₁ = r.next (r.prev a₁ ha₁r')
                  (List.prev_mem r a₁ ha₁r') :=
                (List.next_prev r hrNodup a₁ ha₁r').symm
              _ = b₁ := by simpa [hcPrev] using hbcNext.symm)
      · exact hb₁neC₁ (hbNext.trans hcNext.symm)


end Birkhoff

end FourColor

end Schematic.Math.GraphTheory
