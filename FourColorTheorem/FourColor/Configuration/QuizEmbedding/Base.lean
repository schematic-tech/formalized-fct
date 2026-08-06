
import FourColorTheorem.FourColor.Hypermap.Embedding
import FourColorTheorem.FourColor.Configuration.Quiz

/-!
Quiz-side embedding prerequisites.

This file ports the front of Coq `QuizEmbedding`: the semantic shape of a quiz
that is valid for a kernel set and the immediate consequences of the executable
`fitQuiz` predicate.  The actual `embedqz` morphism is added after the
configuration kernel/ring API is connected to the construction-program maps.
-/

namespace Schematic.Math.GraphTheory





namespace FourColor

namespace Hypermap

universe u

variable (G : Hypermap.{u})

theorem faceClosed_faceBand (s : List G.Dart) :
    G.FaceClosed (G.FaceBand s) := by
  intro x y hx hxy
  exact Hypermap.FaceBand.of_faceReachable (G := G) hx hxy

/-- A quiz valid for a target kernel predicate.  This packages Coq
`valid_quiz`: the quiz is right-rooted, fits the source map, walks a
face-simple list, and its face band is exactly the kernel predicate. -/
structure ValidQuizFor (A : G.Dart → Prop) (x0 : G.Dart) (qz : Quiz) : Prop where
  rightRooted : qz.isQuizR = true
  fits : G.fitQuiz x0 qz = true
  simple : G.FaceSimple (G.walkQuiz x0 qz)
  covers : ∀ y : G.Dart, G.FaceBand (G.walkQuiz x0 qz) y ↔ A y

theorem fitQ_flat_eq_map_arity
    {x : G.Dart} {q : Question}
    (hfit : G.fitQ x q = true) :
    q.flat = (G.walkQ x q).map G.arity := by
  have hb :
      (q.flat == (G.walkQ x q).map G.arity) = true := by
    simpa [Hypermap.fitQ] using hfit
  exact eq_of_beq hb

theorem fitQuiz_flat_eq_map_arity
    {x : G.Dart} {qz : Quiz}
    (hfit : G.fitQuiz x qz = true) :
    qz.flat = (G.walkQuiz x qz).map G.arity := by
  have hb :
      (qz.flat == (G.walkQuiz x qz).map G.arity) = true := by
    simpa [Hypermap.fitQuiz] using hfit
  exact eq_of_beq hb

theorem fitQ_length_eq
    {x : G.Dart} {q : Question} :
    q.flat.length = (G.walkQ x q).length := by
  rw [Hypermap.length_walkQ]

theorem fitQuiz_length_eq
    {x : G.Dart} {qz : Quiz} :
    qz.flat.length = (G.walkQuiz x qz).length := by
  rw [Hypermap.length_walkQuiz]

theorem mem_walkQuiz_root_of_isQuizR
    {x : G.Dart} {qz : Quiz}
    (hR : qz.isQuizR = true) :
    x ∈ G.walkQuiz x qz := by
      cases qz with
      | mk ql qr =>
          cases ql <;> cases qr <;>
        simp [Quiz.isQuizR, Question.isQaskR, Hypermap.walkQuiz,
          Hypermap.walkQ] at hR ⊢

theorem mem_walkQuiz_edge_root_of_isQuizR
    {x : G.Dart} {qz : Quiz}
    (hR : qz.isQuizR = true) :
    G.edge x ∈ G.walkQuiz x qz := by
  cases qz with
  | mk ql qr =>
      cases ql <;> cases qr <;>
        simp [Quiz.isQuizR, Question.isQaskR, Hypermap.walkQuiz,
          Hypermap.walkQ] at hR ⊢

theorem walkQuiz_length_pos_of_isQuizR
    {x : G.Dart} {qz : Quiz}
    (hR : qz.isQuizR = true) :
    0 < (G.walkQuiz x qz).length :=
  List.length_pos_of_mem (G.mem_walkQuiz_root_of_isQuizR hR)

theorem walkQuiz_get_zero_of_isQuizR
    {x : G.Dart} {qz : Quiz}
    (hR : qz.isQuizR = true)
    (hpos : 0 < (G.walkQuiz x qz).length) :
    (G.walkQuiz x qz).get ⟨0, hpos⟩ = x := by
  cases qz with
  | mk ql qr =>
      cases ql <;> cases qr <;>
        simp [Quiz.isQuizR, Question.isQaskR, Hypermap.walkQuiz,
          Hypermap.walkQ] at hR ⊢

theorem walkQuiz_left_length_lt_of_isQuizR
    {x : G.Dart} {qz : Quiz}
    (hR : qz.isQuizR = true) :
    qz.left.flat.length < (G.walkQuiz x qz).length := by
  cases qz with
  | mk ql qr =>
      cases ql <;> cases qr <;>
        simp [Quiz.isQuizR, Question.isQaskR, Hypermap.walkQuiz,
          Hypermap.walkQ, Question.flat] at hR ⊢

theorem walkQuiz_get_left_length_of_isQuizR
    {x : G.Dart} {qz : Quiz}
    (hR : qz.isQuizR = true)
    (hlt : qz.left.flat.length < (G.walkQuiz x qz).length) :
    (G.walkQuiz x qz).get ⟨qz.left.flat.length, hlt⟩ = G.edge x := by
  cases qz with
  | mk ql qr =>
      cases ql <;> cases qr <;>
        simp [Quiz.isQuizR, Question.isQaskR, Hypermap.walkQuiz,
          Hypermap.walkQ, Question.flat] at hR ⊢

/-- First index in a list whose face orbit contains `x`.  This is the list
search part of Coq `embedqz`; it is noncomputable because face reachability is
used propositionally here. -/
noncomputable def firstFaceHitIndex (s : List G.Dart) (x : G.Dart) : Nat := by
  classical
  exact s.findIdx (fun y => decide (PermReachable G.face y x))

theorem firstFaceHitIndex_lt_length_of_faceBand
    {s : List G.Dart} {x : G.Dart}
    (hx : G.FaceBand s x) :
    G.firstFaceHitIndex s x < s.length := by
  classical
  unfold firstFaceHitIndex
  rw [List.findIdx_lt_length]
  rcases hx with ⟨y, hy, hyx⟩
  exact ⟨y, hy, decide_eq_true hyx⟩

theorem firstFaceHitIndex_get_faceReachable
    {s : List G.Dart} {x : G.Dart}
    (hx : G.FaceBand s x) :
    PermReachable G.face
      (s.get ⟨G.firstFaceHitIndex s x,
        G.firstFaceHitIndex_lt_length_of_faceBand hx⟩)
      x := by
  classical
  unfold firstFaceHitIndex
  exact of_decide_eq_true
    (List.findIdx_getElem
      (p := fun y : G.Dart => decide (PermReachable G.face y x))
      (xs := s)
      (w := by
        rw [List.findIdx_lt_length]
        rcases hx with ⟨y, hy, hyx⟩
        exact ⟨y, hy, decide_eq_true hyx⟩))

theorem firstFaceHitIndex_get_mem
    {s : List G.Dart} {x : G.Dart}
    (hx : G.FaceBand s x) :
    (s.get ⟨G.firstFaceHitIndex s x,
      G.firstFaceHitIndex_lt_length_of_faceBand hx⟩) ∈ s :=
  List.get_mem s ⟨G.firstFaceHitIndex s x,
    G.firstFaceHitIndex_lt_length_of_faceBand hx⟩

theorem firstFaceHitIndex_eq_of_faceReachable
    {s : List G.Dart} {x y : G.Dart}
    (hxy : PermReachable G.face x y) :
    G.firstFaceHitIndex s y = G.firstFaceHitIndex s x := by
  classical
  unfold firstFaceHitIndex
  let py : G.Dart → Bool := fun z => decide (PermReachable G.face z y)
  let px : G.Dart → Bool := fun z => decide (PermReachable G.face z x)
  change s.findIdx py = s.findIdx px
  have hiff : ∀ z : G.Dart, py z = true ↔ px z = true := by
    intro z
    constructor
    · intro hzy
      have hz_y : PermReachable G.face z y := by
        simpa [py] using (of_decide_eq_true hzy)
      have hz_x : PermReachable G.face z x :=
        PermReachable.trans G.face hz_y (PermReachable.symm G.face hxy)
      exact decide_eq_true hz_x
    · intro hzx
      have hz_x : PermReachable G.face z x := by
        simpa [px] using (of_decide_eq_true hzx)
      have hz_y : PermReachable G.face z y :=
        PermReachable.trans G.face hz_x hxy
      exact decide_eq_true hz_y
  by_cases hhit : s.findIdx py < s.length
  · have hpx_at : px s[s.findIdx py] = true :=
      (hiff s[s.findIdx py]).1
        (List.findIdx_getElem (p := py) (xs := s) (w := hhit))
    have hpx_min :
        ∀ (j : Nat) (hj : j < s.findIdx py),
          px (s.get ⟨j, Nat.lt_trans hj hhit⟩) = false := by
      intro j hj
      have hjlen : j < s.length := Nat.lt_trans hj hhit
      have hpy_false : py (s.get ⟨j, hjlen⟩) = false := by
        simpa using List.not_of_lt_findIdx (p := py) (xs := s) hj
      change px (s.get ⟨j, hjlen⟩) = false
      cases hpxj : px (s.get ⟨j, hjlen⟩) <;> simp
      have hpy_true : py (s.get ⟨j, hjlen⟩) = true :=
        (hiff (s.get ⟨j, hjlen⟩)).2 hpxj
      rw [hpy_false] at hpy_true
      cases hpy_true
    have hfind_px : s.findIdx px = s.findIdx py :=
      (List.findIdx_eq (p := px) (xs := s) hhit).2
        ⟨hpx_at, hpx_min⟩
    exact hfind_px.symm
  · have hlen_py : s.findIdx py = s.length :=
      le_antisymm List.findIdx_le_length (Nat.le_of_not_gt hhit)
    have hno_py : ∀ z ∈ s, py z = false :=
      (List.findIdx_eq_length (p := py) (xs := s)).1 hlen_py
    have hno_px : ∀ z ∈ s, px z = false := by
      intro z hz
      cases hpxz : px z <;> simp
      have hpy_true : py z = true := (hiff z).2 hpxz
      have hpy_false : py z = false := hno_py z hz
      rw [hpy_false] at hpy_true
      cases hpy_true
    have hlen_px : s.findIdx px = s.length :=
      (List.findIdx_eq_length (p := px) (xs := s)).2 hno_px
    exact hlen_py.trans hlen_px.symm

theorem firstFaceHitIndex_eq_of_faceSimple_get
    {s : List G.Dart}
    (hsimple : G.FaceSimple s)
    {i : Nat}
    (hi : i < s.length) :
    G.firstFaceHitIndex s (s.get ⟨i, hi⟩) = i := by
  classical
  unfold firstFaceHitIndex
  rw [List.findIdx_eq hi]
  constructor
  · exact decide_eq_true (PermReachable.refl G.face (s.get ⟨i, hi⟩))
  · intro j hji
    have hj : j < s.length := Nat.lt_trans hji hi
    rw [decide_eq_false_iff_not]
    intro hreach
    have hpair :=
      (List.pairwise_iff_getElem.mp hsimple) j i hj hi hji
    exact hpair hreach

theorem faceIndex_firstFaceHit_face_eq_succ_mod
    {s : List G.Dart} {x : G.Dart}
    (hx : G.FaceBand s x) :
    G.faceIndex
        (G.firstFaceHitIndex_get_faceReachable
          (s := s)
          (Hypermap.FaceBand.of_faceReachable (G := G) hx
            (PermReachable.forward G.face x))) =
      (G.faceIndex (G.firstFaceHitIndex_get_faceReachable (s := s) hx) + 1) %
        G.arity
          (s.get ⟨G.firstFaceHitIndex s x,
            G.firstFaceHitIndex_lt_length_of_faceBand hx⟩) := by
  classical
  let hxF : G.FaceBand s (G.face x) :=
    Hypermap.FaceBand.of_faceReachable (G := G) hx
      (PermReachable.forward G.face x)
  have hfindF : G.firstFaceHitIndex s (G.face x) =
      G.firstFaceHitIndex s x := by
    exact G.firstFaceHitIndex_eq_of_faceReachable (s := s)
      (PermReachable.forward G.face x)
  let y : G.Dart :=
    s.get ⟨G.firstFaceHitIndex s x,
      G.firstFaceHitIndex_lt_length_of_faceBand hx⟩
  let hreach : PermReachable G.face y x :=
    G.firstFaceHitIndex_get_faceReachable (s := s) hx
  have hiter :
      ((G.face : G.Dart → G.Dart)^[
        (G.faceIndex hreach + 1) % G.arity y]) y = G.face x := by
    calc
      ((G.face : G.Dart → G.Dart)^[
        (G.faceIndex hreach + 1) % G.arity y]) y =
          G.face (((G.face : G.Dart → G.Dart)^[G.faceIndex hreach]) y) := by
            exact G.face_iterate_succ_mod_arity_eq y (G.faceIndex hreach)
      _ = G.face x := by
            exact congrArg G.face (G.face_iter_faceIndex hreach)
  apply G.faceIndex_eq_of_iterate_eq_lt_arity
  · simpa [hfindF, y, hxF] using
      Nat.mod_lt (G.faceIndex hreach + 1) (G.arity_pos y)
  · simpa [hfindF, y, hreach, hxF] using hiter

variable (H : Hypermap.{u})

/-- The Coq `embedqz` map skeleton: a dart in the quiz face-band is sent to
the corresponding dart in the target walk, advanced by the same source
face-orbit index.  The preservation proofs are developed as the surrounding
kernel/ring API is connected. -/
noncomputable def embedQuiz
    (x0G : G.Dart) (x0H : H.Dart) (qz : Quiz)
    (x : G.Dart) (hx : G.FaceBand (G.walkQuiz x0G qz) x) :
    H.Dart := by
  classical
  let sG := G.walkQuiz x0G qz
  let sH := H.walkQuiz x0H qz
  let i := G.firstFaceHitIndex sG x
  have hltG : i < sG.length := by
    simpa [i, sG] using
      G.firstFaceHitIndex_lt_length_of_faceBand
        (s := G.walkQuiz x0G qz) hx
  have hltH : i < sH.length := by
    have hlenG : sG.length = qz.flat.length := by
      simp [sG]
    have hlenH : sH.length = qz.flat.length := by
      simp [sH]
    omega
  have hreach : PermReachable G.face (sG.get ⟨i, hltG⟩) x := by
    simpa [i, sG] using
      G.firstFaceHitIndex_get_faceReachable
        (s := G.walkQuiz x0G qz) hx
  exact ((H.face : H.Dart → H.Dart)^[G.faceIndex hreach])
    (sH.get ⟨i, hltH⟩)

theorem embedQuiz_faceReachable_selected
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    {x : G.Dart}
    (hx : G.FaceBand (G.walkQuiz x0G qz) x)
    {i : Nat}
    (hi : i = G.firstFaceHitIndex (G.walkQuiz x0G qz) x)
    (hiH : i < (H.walkQuiz x0H qz).length) :
    PermReachable H.face
      ((H.walkQuiz x0H qz).get ⟨i, hiH⟩)
      (G.embedQuiz H x0G x0H qz x hx) := by
  subst i
  unfold embedQuiz
  dsimp only
  exact permReachable_of_iterate_eq H.face rfl

theorem embedQuiz_eq_of_faceBand_proof
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    {x : G.Dart}
    (hx₁ hx₂ : G.FaceBand (G.walkQuiz x0G qz) x) :
    G.embedQuiz H x0G x0H qz x hx₁ =
      G.embedQuiz H x0G x0H qz x hx₂ := by
  classical
  let sG := G.walkQuiz x0G qz
  let i := G.firstFaceHitIndex sG x
  have hltG₁ : i < sG.length := by
    simpa [i, sG] using
      G.firstFaceHitIndex_lt_length_of_faceBand
        (s := G.walkQuiz x0G qz) hx₁
  have hltG₂ : i < sG.length := by
    simpa [i, sG] using
      G.firstFaceHitIndex_lt_length_of_faceBand
        (s := G.walkQuiz x0G qz) hx₂
  let yG : G.Dart := sG.get ⟨i, hltG₁⟩
  let hreach₁ : PermReachable G.face yG x := by
    simpa [i, sG, yG] using
      G.firstFaceHitIndex_get_faceReachable
        (s := G.walkQuiz x0G qz) hx₁
  let hreach₂ : PermReachable G.face (sG.get ⟨i, hltG₂⟩) x := by
    simpa [i, sG] using
      G.firstFaceHitIndex_get_faceReachable
        (s := G.walkQuiz x0G qz) hx₂
  have hidx : G.faceIndex hreach₂ = G.faceIndex hreach₁ := by
    apply G.faceIndex_eq_of_iterate_eq_lt_arity
    · simpa [yG] using G.faceIndex_lt_arity hreach₁
    · simpa [yG, hreach₁, hreach₂] using G.face_iter_faceIndex hreach₁
  unfold embedQuiz
  dsimp only

theorem walkQuiz_get_arity_eq_of_fitQuiz
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hfitG : G.fitQuiz x0G qz = true)
    (hfitH : H.fitQuiz x0H qz = true)
    {i : Nat}
    (hiG : i < (G.walkQuiz x0G qz).length)
    (hiH : i < (H.walkQuiz x0H qz).length) :
    H.arity ((H.walkQuiz x0H qz).get ⟨i, hiH⟩) =
      G.arity ((G.walkQuiz x0G qz).get ⟨i, hiG⟩) := by
  have hG := Hypermap.fitQuiz_flat_eq_map_arity (G := G) hfitG
  have hH := Hypermap.fitQuiz_flat_eq_map_arity (G := H) hfitH
  have hmap :
      (H.walkQuiz x0H qz).map H.arity =
        (G.walkQuiz x0G qz).map G.arity := by
    rw [← hH, hG]
  have hget := congrArg (fun xs : List Nat => xs[i]?) hmap
  change ((H.walkQuiz x0H qz).map H.arity)[i]? =
    ((G.walkQuiz x0G qz).map G.arity)[i]? at hget
  rw [List.getElem?_map, List.getElem?_map] at hget
  rw [List.getElem?_eq_getElem hiH, List.getElem?_eq_getElem hiG] at hget
  simpa using hget

theorem embedQuiz_arity_of_fitQuiz
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hfitG : G.fitQuiz x0G qz = true)
    (hfitH : H.fitQuiz x0H qz = true)
    {x : G.Dart}
    (hx : G.FaceBand (G.walkQuiz x0G qz) x) :
    H.arity (G.embedQuiz H x0G x0H qz x hx) = G.arity x := by
  classical
  let sG := G.walkQuiz x0G qz
  let sH := H.walkQuiz x0H qz
  let i := G.firstFaceHitIndex sG x
  have hltG : i < sG.length := by
    simpa [i, sG] using
      G.firstFaceHitIndex_lt_length_of_faceBand
        (s := G.walkQuiz x0G qz) hx
  have hltH : i < sH.length := by
    have hlenG : sG.length = qz.flat.length := by
      simp [sG]
    have hlenH : sH.length = qz.flat.length := by
      simp [sH]
    omega
  have hreach : PermReachable G.face (sG.get ⟨i, hltG⟩) x := by
    simpa [i, sG] using
      G.firstFaceHitIndex_get_faceReachable
        (s := G.walkQuiz x0G qz) hx
  have htargetReach :
      PermReachable H.face (sH.get ⟨i, hltH⟩)
        (((H.face : H.Dart → H.Dart)^[G.faceIndex hreach])
          (sH.get ⟨i, hltH⟩)) :=
    permReachable_of_iterate_eq H.face rfl
  change
    H.arity
        (((H.face : H.Dart → H.Dart)^[G.faceIndex hreach])
          (sH.get ⟨i, hltH⟩)) =
      G.arity x
  calc
    H.arity
        (((H.face : H.Dart → H.Dart)^[G.faceIndex hreach])
          (sH.get ⟨i, hltH⟩)) =
        H.arity (sH.get ⟨i, hltH⟩) := by
          exact (H.arity_eq_of_faceReachable htargetReach).symm
    _ = G.arity (sG.get ⟨i, hltG⟩) := by
          exact walkQuiz_get_arity_eq_of_fitQuiz
            (G := G) (H := H) (x0G := x0G) (x0H := x0H)
            (qz := qz) hfitG hfitH
            (by simpa [sG] using hltG)
            (by simpa [sH] using hltH)
    _ = G.arity x := by
          exact G.arity_eq_of_faceReachable hreach

theorem embedQuiz_face_of_fitQuiz
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hfitG : G.fitQuiz x0G qz = true)
    (hfitH : H.fitQuiz x0H qz = true)
    {x : G.Dart}
    (hx : G.FaceBand (G.walkQuiz x0G qz) x) :
    G.embedQuiz H x0G x0H qz (G.face x)
        (Hypermap.FaceBand.of_faceReachable (G := G) hx
          (PermReachable.forward G.face x)) =
      H.face (G.embedQuiz H x0G x0H qz x hx) := by
  classical
  let sG := G.walkQuiz x0G qz
  let sH := H.walkQuiz x0H qz
  let hxF : G.FaceBand sG (G.face x) :=
    Hypermap.FaceBand.of_faceReachable (G := G) (by simpa [sG] using hx)
      (PermReachable.forward G.face x)
  let i := G.firstFaceHitIndex sG x
  have hfindF : G.firstFaceHitIndex sG (G.face x) = i := by
    simpa [i] using
      G.firstFaceHitIndex_eq_of_faceReachable (s := sG)
        (PermReachable.forward G.face x)
  have hltG : i < sG.length := by
    simpa [i, sG] using
      G.firstFaceHitIndex_lt_length_of_faceBand
        (s := G.walkQuiz x0G qz) hx
  have hltH : i < sH.length := by
    have hlenG : sG.length = qz.flat.length := by
      simp [sG]
    have hlenH : sH.length = qz.flat.length := by
      simp [sH]
    omega
  let yG : G.Dart := sG.get ⟨i, hltG⟩
  let yH : H.Dart := sH.get ⟨i, hltH⟩
  let hreach : PermReachable G.face yG x := by
    simpa [i, sG, yG] using
      G.firstFaceHitIndex_get_faceReachable
        (s := G.walkQuiz x0G qz) hx
  have hidxF :
      G.faceIndex
          (G.firstFaceHitIndex_get_faceReachable
            (s := G.walkQuiz x0G qz)
            (Hypermap.FaceBand.of_faceReachable (G := G) hx
              (PermReachable.forward G.face x))) =
        (G.faceIndex hreach + 1) % G.arity yG := by
    simpa [sG, yG, hreach] using
      G.faceIndex_firstFaceHit_face_eq_succ_mod
        (s := G.walkQuiz x0G qz) (x := x) hx
  have harity : H.arity yH = G.arity yG := by
    exact walkQuiz_get_arity_eq_of_fitQuiz
      (G := G) (H := H) (x0G := x0G) (x0H := x0H)
      (qz := qz) hfitG hfitH
      (by simpa [sG] using hltG)
      (by simpa [sH] using hltH)
  have hiterH :
      ((H.face : H.Dart → H.Dart)^[
        (G.faceIndex hreach + 1) % G.arity yG]) yH =
        H.face (((H.face : H.Dart → H.Dart)^[G.faceIndex hreach]) yH) := by
    calc
      ((H.face : H.Dart → H.Dart)^[
        (G.faceIndex hreach + 1) % G.arity yG]) yH =
          ((H.face : H.Dart → H.Dart)^[
            (G.faceIndex hreach + 1) % H.arity yH]) yH := by
            rw [← harity]
      _ = H.face (((H.face : H.Dart → H.Dart)^[G.faceIndex hreach]) yH) := by
            exact H.face_iterate_succ_mod_arity_eq yH (G.faceIndex hreach)
  unfold embedQuiz
  dsimp only
  rw [hidxF]
  simpa [sG, sH, hxF, i, yG, yH, hfindF, hreach] using hiterH

theorem embedQuiz_walk_get_of_faceSimple
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hsimple : G.FaceSimple (G.walkQuiz x0G qz))
    {i : Nat}
    (hiG : i < (G.walkQuiz x0G qz).length)
    (hiH : i < (H.walkQuiz x0H qz).length) :
    G.embedQuiz H x0G x0H qz
        ((G.walkQuiz x0G qz).get ⟨i, hiG⟩)
        (Hypermap.FaceBand.of_mem (G := G)
          (List.get_mem (G.walkQuiz x0G qz) ⟨i, hiG⟩)
          (PermReachable.refl G.face
            ((G.walkQuiz x0G qz).get ⟨i, hiG⟩))) =
      (H.walkQuiz x0H qz).get ⟨i, hiH⟩ := by
  classical
  let sG := G.walkQuiz x0G qz
  let sH := H.walkQuiz x0H qz
  let x := sG.get ⟨i, by simpa [sG] using hiG⟩
  let hx : G.FaceBand sG x :=
    Hypermap.FaceBand.of_mem (G := G)
      (List.get_mem sG ⟨i, by simpa [sG] using hiG⟩)
      (PermReachable.refl G.face x)
  have hfind :
      G.firstFaceHitIndex sG x = i := by
    simpa [x, sG] using
      G.firstFaceHitIndex_eq_of_faceSimple_get
        (s := G.walkQuiz x0G qz) hsimple hiG
  have hltFind : G.firstFaceHitIndex sG x < sG.length :=
    G.firstFaceHitIndex_lt_length_of_faceBand hx
  have hfin :
      (⟨G.firstFaceHitIndex sG x, hltFind⟩ : Fin sG.length) =
        ⟨i, by simpa [sG] using hiG⟩ := by
    exact Fin.ext hfind
  have hreach :
      PermReachable G.face
        (sG.get ⟨G.firstFaceHitIndex sG x, hltFind⟩) x :=
    G.firstFaceHitIndex_get_faceReachable hx
  have hselected :
      sG.get ⟨G.firstFaceHitIndex sG x, hltFind⟩ = x := by
    rw [hfin]
  have hzero : G.faceIndex hreach = 0 :=
    G.faceIndex_eq_zero_of_eq hreach hselected
  unfold embedQuiz
  dsimp only
  simp only [sG] at hfind hzero ⊢
  simp only [hzero, Function.iterate_zero_apply]
  apply congrArg (List.get (H.walkQuiz x0H qz))
  exact Fin.ext hfind

theorem embedQuiz_walk_get_of_eq
    {x0G : G.Dart} {x0H : H.Dart} {qz : Quiz}
    (hsimple : G.FaceSimple (G.walkQuiz x0G qz))
    {i : Nat}
    (hiG : i < (G.walkQuiz x0G qz).length)
    (hiH : i < (H.walkQuiz x0H qz).length)
    {x : G.Dart}
    (hx : G.FaceBand (G.walkQuiz x0G qz) x)
    (hxeq : x = (G.walkQuiz x0G qz).get ⟨i, hiG⟩) :
    G.embedQuiz H x0G x0H qz x hx =
      (H.walkQuiz x0H qz).get ⟨i, hiH⟩ := by
  subst x
  calc
    G.embedQuiz H x0G x0H qz
        ((G.walkQuiz x0G qz).get ⟨i, hiG⟩) hx =
        G.embedQuiz H x0G x0H qz
          ((G.walkQuiz x0G qz).get ⟨i, hiG⟩)
          (Hypermap.FaceBand.of_mem (G := G)
            (List.get_mem (G.walkQuiz x0G qz) ⟨i, hiG⟩)
            (PermReachable.refl G.face
              ((G.walkQuiz x0G qz).get ⟨i, hiG⟩))) := by
          exact G.embedQuiz_eq_of_faceBand_proof (H := H) hx
            (Hypermap.FaceBand.of_mem (G := G)
              (List.get_mem (G.walkQuiz x0G qz) ⟨i, hiG⟩)
              (PermReachable.refl G.face
                ((G.walkQuiz x0G qz).get ⟨i, hiG⟩)))
    _ = (H.walkQuiz x0H qz).get ⟨i, hiH⟩ :=
          G.embedQuiz_walk_get_of_faceSimple (H := H)
            (x0G := x0G) (x0H := x0H) (qz := qz)
            hsimple hiG hiH


end Hypermap

end FourColor

end Schematic.Math.GraphTheory
