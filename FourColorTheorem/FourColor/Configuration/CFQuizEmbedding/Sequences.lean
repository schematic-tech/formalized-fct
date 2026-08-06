import FourColorTheorem.FourColor.Configuration.CFQuizEmbedding.QuestionCases

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace CFQuiz

open Hypermap

@[simp]
theorem rqSeqFits_nil_nil
    (G0 G : Hypermap) (h : G.Dart → G0.Dart) :
    rqSeqFits G0 G h [] [] = true :=
  rfl

@[simp]
theorem rqSeqFits_cons_cons
    (G0 G : Hypermap) (h : G.Dart → G0.Dart)
    (rq : RingQuestion) (qs : RqSeq) (x : G.Dart) (xs : List G.Dart) :
    rqSeqFits G0 G h (rq :: qs) (x :: xs) =
      ((G0.arity (h x) == rq.outerArity + G.arity x) &&
        G0.fitQ (G0.node (h x)) rq.nodeQuestion &&
          rqSeqFits G0 G h qs xs) :=
  rfl

theorem rqSeqFits_length_eq
    {G0 G : Hypermap} {h : G.Dart → G0.Dart} :
    ∀ {qs : RqSeq} {xs : List G.Dart},
      rqSeqFits G0 G h qs xs = true → qs.length = xs.length
  | [], [], _ => rfl
  | [], _ :: _, hfit => by
      simp [rqSeqFits] at hfit
  | _ :: _, [], hfit => by
      simp [rqSeqFits] at hfit
  | rq :: qs, x :: xs, hfit => by
      have htail :
          rqSeqFits G0 G h qs xs = true := by
        simp [rqSeqFits] at hfit
        exact hfit.2
      simpa using congrArg Nat.succ
        (rqSeqFits_length_eq (G0 := G0) (G := G) (h := h)
          (qs := qs) (xs := xs) htail)

theorem rqSeqFits_head_arity
    {G0 G : Hypermap} {h : G.Dart → G0.Dart}
    {rq : RingQuestion} {qs : RqSeq} {x : G.Dart} {xs : List G.Dart}
    (hfit : rqSeqFits G0 G h (rq :: qs) (x :: xs) = true) :
    G0.arity (h x) = rq.outerArity + G.arity x := by
  simp [rqSeqFits] at hfit
  exact hfit.1.1

theorem rqSeqFits_head_fitQ
    {G0 G : Hypermap} {h : G.Dart → G0.Dart}
    {rq : RingQuestion} {qs : RqSeq} {x : G.Dart} {xs : List G.Dart}
    (hfit : rqSeqFits G0 G h (rq :: qs) (x :: xs) = true) :
    G0.fitQ (G0.node (h x)) rq.nodeQuestion = true := by
  simp [rqSeqFits] at hfit
  exact hfit.1.2

theorem rqSeqFits_tail
    {G0 G : Hypermap} {h : G.Dart → G0.Dart}
    {rq : RingQuestion} {qs : RqSeq} {x : G.Dart} {xs : List G.Dart}
    (hfit : rqSeqFits G0 G h (rq :: qs) (x :: xs) = true) :
    rqSeqFits G0 G h qs xs = true := by
  simp [rqSeqFits] at hfit
  exact hfit.2

theorem rqSeqFits_append
    (G0 G : Hypermap) (h : G.Dart → G0.Dart) :
    ∀ (qs₁ qs₂ : RqSeq) (xs₁ xs₂ : List G.Dart),
      qs₁.length = xs₁.length →
        rqSeqFits G0 G h (qs₁ ++ qs₂) (xs₁ ++ xs₂) =
          (rqSeqFits G0 G h qs₁ xs₁ &&
            rqSeqFits G0 G h qs₂ xs₂)
  | [], qs₂, [], xs₂, _hlen => by
      simp [rqSeqFits]
  | [], _qs₂, _x :: _xs₁, _xs₂, hlen => by
      simp at hlen
  | _rq :: _qs₁, _qs₂, [], _xs₂, hlen => by
      simp at hlen
  | rq :: qs₁, qs₂, x :: xs₁, xs₂, hlen => by
      have htail : qs₁.length = xs₁.length := by
        simpa using Nat.succ.inj hlen
      simp [rqSeqFits, rqSeqFits_append G0 G h qs₁ qs₂ xs₁ xs₂ htail,
        Bool.and_assoc]

/-- Transport a ring-question fit through a source-dart embedding that
preserves the source face arity on the displayed roots. -/
theorem rqSeqFits_comp_of_arity_eq
    (G0 G G' : Hypermap) (h : G'.Dart → G0.Dart)
    (f : G.Dart → G'.Dart) :
    ∀ (qs : RqSeq) (xs : List G.Dart),
      (∀ x : G.Dart, x ∈ xs → G'.arity (f x) = G.arity x) →
        rqSeqFits G0 G (fun x => h (f x)) qs xs =
          rqSeqFits G0 G' h qs (xs.map f)
  | [], [], _harity => by simp [rqSeqFits]
  | [], _x :: _xs, _harity => by simp [rqSeqFits]
  | _rq :: _qs, [], _harity => by simp [rqSeqFits]
  | rq :: qs, x :: xs, harity => by
      have hx := harity x (List.Mem.head xs)
      have htail :
          ∀ y : G.Dart, y ∈ xs → G'.arity (f y) = G.arity y :=
        fun y hy => harity y (List.Mem.tail x hy)
      simp [rqSeqFits, hx,
        rqSeqFits_comp_of_arity_eq G0 G G' h f qs xs htail]

theorem rqSeqFits_rqsY
    (G0 G : Hypermap) (h : G.Dart → G0.Dart)
    (rq1 rq3 : RingQuestion) (qs : RqSeq)
    (q1' : Question) (x1 x3 : G.Dart) (xs : List G.Dart) :
    rqSeqFits G0 G h (rqsY rq1 rq3 qs q1') (x1 :: x3 :: xs) =
      ((G0.arity (h x1) == (rq1.outerArity + 1) + G.arity x1) &&
        G0.fitQ (G0.node (h x1)) q1' &&
          (G0.arity (h x3) == (rq3.outerArity + 1) + G.arity x3) &&
            G0.fitQ (G0.node (h x3)) rq3.nodeQuestion &&
              rqSeqFits G0 G h qs xs) := by
  simp [rqsY, rqSeqFits, Bool.and_assoc]

theorem rqSeqFits_rqsH
    (G0 G : Hypermap) (h : G.Dart → G0.Dart)
    (rq1 rq3 : RingQuestion) (qs : RqSeq)
    (q1' q2' : Question) (x1 x2 x3 : G.Dart) (xs : List G.Dart) :
    rqSeqFits G0 G h (rqsH rq1 rq3 qs q1' q2')
      (x1 :: x2 :: x3 :: xs) =
        ((G0.arity (h x1) == (rq1.outerArity + 1) + G.arity x1) &&
          G0.fitQ (G0.node (h x1)) q1' &&
            (G0.arity (h x2) == 1 + G.arity x2) &&
              G0.fitQ (G0.node (h x2)) q2' &&
                (G0.arity (h x3) == (rq3.outerArity + 1) + G.arity x3) &&
                  G0.fitQ (G0.node (h x3)) rq3.nodeQuestion &&
                    rqSeqFits G0 G h qs xs) := by
  simp [rqsH, rqSeqFits, Bool.and_assoc]

/-- Coq `rqs_walk`: the darts visited by a ring-question sequence rooted at
the corresponding ring representatives. -/
def rqSeqWalk (G : Hypermap) : RqSeq → List G.Dart → List G.Dart
  | rq :: qs, u :: us =>
      (if rq.isKernel then [u] else []) ++
        G.walkQ (G.node u) rq.nodeQuestion ++
          rqSeqWalk G qs us
  | _, _ => []

@[simp]
theorem rqSeqWalk_cons_cons
    (G : Hypermap) (rq : RingQuestion) (qs : RqSeq)
    (u : G.Dart) (us : List G.Dart) :
    rqSeqWalk G (rq :: qs) (u :: us) =
      (if rq.isKernel then [u] else []) ++
        G.walkQ (G.node u) rq.nodeQuestion ++
          rqSeqWalk G qs us :=
  rfl

theorem rqSeqWalk_append
    (G : Hypermap) :
    ∀ (qs₁ qs₂ : RqSeq) (xs₁ xs₂ : List G.Dart),
      qs₁.length = xs₁.length →
        rqSeqWalk G (qs₁ ++ qs₂) (xs₁ ++ xs₂) =
          rqSeqWalk G qs₁ xs₁ ++ rqSeqWalk G qs₂ xs₂
  | [], qs₂, [], xs₂, _hlen => by
      simp [rqSeqWalk]
  | [], _qs₂, _x :: _xs₁, _xs₂, hlen => by
      simp at hlen
  | _rq :: _qs₁, _qs₂, [], _xs₂, hlen => by
      simp at hlen
  | rq :: qs₁, qs₂, x :: xs₁, xs₂, hlen => by
      have htail : qs₁.length = xs₁.length := by
        simpa using Nat.succ.inj hlen
      simp [rqSeqWalk, rqSeqWalk_append G qs₁ qs₂ xs₁ xs₂ htail,
        List.append_assoc]

theorem rqSeqFits_rotateRight
    (G0 G : Hypermap) (h : G.Dart → G0.Dart)
    (n : Nat) (qs : RqSeq) (xs : List G.Dart)
    (hlen : qs.length = xs.length) :
    rqSeqFits G0 G h (CProg.rotateRight n qs)
        (CProg.rotateRight n xs) = rqSeqFits G0 G h qs xs := by
  let k := qs.length - n
  have hk : xs.length - n = k := by simp [k, hlen]
  have hdrop : (qs.drop k).length = (xs.drop k).length := by
    simp [hlen]
  have htake : (qs.take k).length = (xs.take k).length := by
    simp [hlen]
  change
    rqSeqFits G0 G h
      (qs.drop k ++ qs.take k)
      (xs.drop (xs.length - n) ++ xs.take (xs.length - n)) = _
  rw [hk]
  calc
    rqSeqFits G0 G h (qs.drop k ++ qs.take k)
          (xs.drop k ++ xs.take k) =
        (rqSeqFits G0 G h (qs.drop k) (xs.drop k) &&
          rqSeqFits G0 G h (qs.take k) (xs.take k)) :=
      rqSeqFits_append G0 G h _ _ _ _ hdrop
    _ = (rqSeqFits G0 G h (qs.take k) (xs.take k) &&
          rqSeqFits G0 G h (qs.drop k) (xs.drop k)) :=
      Bool.and_comm _ _
    _ = rqSeqFits G0 G h
          (qs.take k ++ qs.drop k) (xs.take k ++ xs.drop k) :=
      (rqSeqFits_append G0 G h _ _ _ _ htake).symm
    _ = rqSeqFits G0 G h qs xs := by
      rw [List.take_append_drop, List.take_append_drop]

theorem rqSeqWalk_rotateRight_perm
    (G : Hypermap) (n : Nat) (qs : RqSeq) (xs : List G.Dart)
    (hlen : qs.length = xs.length) :
    (rqSeqWalk G (CProg.rotateRight n qs)
      (CProg.rotateRight n xs)).Perm (rqSeqWalk G qs xs) := by
  let k := qs.length - n
  have hk : xs.length - n = k := by simp [k, hlen]
  have hdrop : (qs.drop k).length = (xs.drop k).length := by
    simp [hlen]
  have htake : (qs.take k).length = (xs.take k).length := by
    simp [hlen]
  change
    (rqSeqWalk G
      (qs.drop k ++ qs.take k)
      (xs.drop (xs.length - n) ++ xs.take (xs.length - n))).Perm _
  rw [hk, rqSeqWalk_append G _ _ _ _ hdrop]
  have hswap :
      (rqSeqWalk G (qs.drop k) (xs.drop k) ++
        rqSeqWalk G (qs.take k) (xs.take k)).Perm
      (rqSeqWalk G (qs.take k) (xs.take k) ++
        rqSeqWalk G (qs.drop k) (xs.drop k)) :=
    List.perm_append_comm
  have hreconstruct :
      rqSeqWalk G (qs.take k) (xs.take k) ++
          rqSeqWalk G (qs.drop k) (xs.drop k) =
        rqSeqWalk G qs xs := by
    rw [← rqSeqWalk_append G _ _ _ _ htake,
      List.take_append_drop, List.take_append_drop]
  exact hswap.trans (List.Perm.of_eq hreconstruct)

theorem rqSeqWalk_rqsY
    (G : Hypermap) (rq1 rq3 : RingQuestion) (qs : RqSeq)
    (q1' : Question) (u1 u3 : G.Dart) (us : List G.Dart) :
    rqSeqWalk G (rqsY rq1 rq3 qs q1') (u1 :: u3 :: us) =
      (if rq1.isKernel then [u1] else []) ++
        G.walkQ (G.node u1) q1' ++
          (if rq3.isKernel then [u3] else []) ++
            G.walkQ (G.node u3) rq3.nodeQuestion ++
              rqSeqWalk G qs us := by
  simp [rqsY, rqSeqWalk, List.append_assoc]

theorem rqSeqWalk_rqsH
    (G : Hypermap) (rq1 rq3 : RingQuestion) (qs : RqSeq)
    (q1' q2' : Question) (u1 u2 u3 : G.Dart) (us : List G.Dart) :
    rqSeqWalk G (rqsH rq1 rq3 qs q1' q2') (u1 :: u2 :: u3 :: us) =
      (if rq1.isKernel then [u1] else []) ++
        G.walkQ (G.node u1) q1' ++
          [u2] ++ G.walkQ (G.node u2) q2' ++
            (if rq3.isKernel then [u3] else []) ++
              G.walkQ (G.node u3) rq3.nodeQuestion ++
                rqSeqWalk G qs us := by
  simp [rqsH, rqSeqWalk, List.append_assoc]

theorem rqSeqFits_initialRingQuestions_id
    (G : Hypermap) :
    ∀ r : List G.Dart,
      rqSeqFits G G (fun x => x)
        (initialRingQuestions r.length) r = true
  | [] => by
      simp [initialRingQuestions]
  | x :: xs => by
      change
        rqSeqFits G G (fun x => x)
          ({ isKernel := false, outerArity := 0,
              nodeQuestion := Question.Qask0 } ::
            initialRingQuestions xs.length) (x :: xs) = true
      simp [rqSeqFits, rqSeqFits_initialRingQuestions_id G xs]

theorem rqSeqWalk_initialRingQuestions
    (G : Hypermap) :
    ∀ r : List G.Dart,
      rqSeqWalk G (initialRingQuestions r.length) r = []
  | [] => by
      simp [initialRingQuestions, rqSeqWalk]
  | x :: xs => by
      change
        rqSeqWalk G
          ({ isKernel := false, outerArity := 0,
              nodeQuestion := Question.Qask0 } ::
            initialRingQuestions xs.length) (x :: xs) = []
      simp [rqSeqWalk, Hypermap.walkQ, rqSeqWalk_initialRingQuestions G xs]

/-- Predicate-valued codomain of the ring injection used in Coq
`rqs_proper`. -/
def RqSeqCodom {G0 G : Hypermap} (h : G.Dart → G0.Dart)
    (x : G0.Dart) : Prop :=
  ∃ y : G.Dart, h y = x

/-- Target predicate represented by Coq
`[predU [predC codom h] & fband (map h r)]` in `rqs_proper`. -/
def RqSeqTarget {G0 G : Hypermap} (h : G.Dart → G0.Dart)
    (r : List G.Dart) (x : G0.Dart) : Prop :=
  ¬ RqSeqCodom h x ∨ G0.FaceBand (r.map h) x

/-- Coq `EpY1`: after deleting the two fresh `ecpY` darts, the union of
the complement of the old-dart image and the mapped perimeter face band is
unchanged. -/
theorem rqSeqTarget_comp_yOld_iff
    (P : PointedHypermap) {G0 : Hypermap}
    (h : P.y.map.Dart → G0.Dart)
    (hface : ∀ x y : P.y.map.Dart,
      PermReachable G0.face (h x) (h y) ↔
        PermReachable P.y.map.face x y)
    (r : List P.map.Dart)
    (hr : r = P.map.node P.point :: P.point :: r.drop 2)
    (u : G0.Dart) :
    RqSeqTarget (fun x => h (P.yOld x)) r u ↔
      RqSeqTarget h
        (P.y.map.node P.y.point :: P.y.point ::
          (r.drop 1).map P.yOld) u := by
  have hdrop : r.drop 1 = P.point :: r.drop 2 := by
    calc
      r.drop 1 =
          (P.map.node P.point :: P.point :: r.drop 2).drop 1 :=
        congrArg (List.drop 1) hr
      _ = P.point :: r.drop 2 := rfl
  have hnodeOld :
      PermReachable P.y.map.face (P.y.map.node P.y.point)
        (P.yOld (P.map.node P.point)) :=
    (PointedHypermap.y_faceReachable_node_point_old_iff P).2
      (PermReachable.refl P.map.face (P.map.node P.point))
  have hpointOldNew :
      PermReachable P.y.map.face P.y.point
        (ExtDart.old ExtDart.new) := by
    change PermReachable
      (Hypermap.extensionN (Hypermap.extensionU P.map P.point)
        ExtDart.new).face ExtDart.new (ExtDart.old ExtDart.new)
    exact Hypermap.extensionN_faceReachable_new_old_x0
      (G := Hypermap.extensionU P.map P.point) ExtDart.new
  have holdPointNewEdge :
      PermReachable P.y.map.face (P.yOld P.point) ExtDart.newEdge :=
    (PointedHypermap.yOld_faceReachable_newEdge_iff P).2
      (PermReachable.refl P.map.face P.point)
  have hnewNodeEq :
      (ExtDart.old ExtDart.newEdge : P.y.map.Dart) =
        P.y.map.node P.y.point := by
    change ExtDart.old ExtDart.newEdge =
      (Hypermap.extensionY P.map P.point).node ExtDart.new
    rw [Hypermap.extensionY_node_new]
  constructor
  · rintro (houtside | hband)
    · by_cases houtsideOld : ¬ RqSeqCodom h u
      · exact Or.inl houtsideOld
      · have hcodom : RqSeqCodom h u :=
          Classical.byContradiction houtsideOld
        rcases hcodom with ⟨y, rfl⟩
        apply Or.inr
        cases y with
        | new =>
            exact Hypermap.FaceBand.of_mem (G := G0)
              (List.Mem.tail _ (List.Mem.head _))
              (PermReachable.refl G0.face (h P.y.point))
        | newEdge =>
            refine Hypermap.FaceBand.of_mem (G := G0)
              (x := h (P.yOld P.point))
              (u := h (ExtDart.newEdge : P.y.map.Dart)) ?_ ?_
            · simp only [List.map_cons, List.mem_cons, List.mem_map]
              have hp : P.point ∈ r.drop 1 := by
                rw [hdrop]
                exact List.Mem.head _
              exact Or.inr (Or.inr
                ⟨P.yOld P.point,
                  ⟨P.point, hp, rfl⟩, rfl⟩)
            · exact (hface _ _).2 holdPointNewEdge
        | old y =>
            cases y with
            | new =>
                exact Hypermap.FaceBand.of_mem (G := G0)
                  (List.Mem.tail _ (List.Mem.head _))
                  ((hface _ _).2 hpointOldNew)
            | newEdge =>
                rw [hnewNodeEq]
                exact Hypermap.FaceBand.of_mem (G := G0)
                  (List.Mem.head _)
                  (PermReachable.refl G0.face
                    (h (P.y.map.node P.y.point)))
            | old x =>
                exact False.elim (houtside ⟨x, rfl⟩)
    · rcases hband with ⟨z, hz, hzu⟩
      rcases List.mem_map.mp hz with ⟨x, hx, rfl⟩
      apply Or.inr
      rw [hr] at hx
      rcases List.mem_cons.mp hx with rfl | hx
      · refine Hypermap.FaceBand.of_mem (G := G0) (List.Mem.head _) ?_
        exact PermReachable.trans G0.face ((hface _ _).2 hnodeOld) hzu
      · refine Hypermap.FaceBand.of_mem (G := G0) ?_ hzu
        simp only [List.map_cons, List.mem_cons, List.mem_map]
        have hxDrop : x ∈ r.drop 1 := by
          rw [hdrop]
          exact hx
        exact Or.inr (Or.inr
          ⟨P.yOld x, ⟨x, hxDrop, rfl⟩, rfl⟩)
  · rintro (houtside | hband)
    · exact Or.inl (fun ⟨x, hx⟩ => houtside ⟨P.yOld x, hx⟩)
    · rcases hband with ⟨z, hz, hzu⟩
      obtain ⟨y, hy, hyz⟩ := List.mem_map.mp hz
      subst z
      have hz' :
          y = P.y.map.node P.y.point ∨ y = P.y.point ∨
            y ∈ (r.drop 1).map P.yOld := by
        simpa only [List.mem_cons] using hy
      rcases hz' with rfl | rfl | hz
      · by_cases hcodom : RqSeqCodom (fun x => h (P.yOld x)) u
        · rcases hcodom with ⟨x, rfl⟩
          apply Or.inr
          refine Hypermap.FaceBand.of_mem (G := G0)
            (x := h (P.yOld (P.map.node P.point)))
            (u := h (P.yOld x)) ?_ ?_
          · rw [hr]
            exact List.Mem.head _
          · have hyx :
                PermReachable P.y.map.face
                  (P.y.map.node P.y.point) (P.yOld x) :=
              (hface _ _).1 hzu
            have hold :
                PermReachable P.map.face (P.map.node P.point) x :=
              (PointedHypermap.y_faceReachable_node_point_old_iff P).1 hyx
            exact (hface _ _).2
              ((PointedHypermap.yOld_faceReachable_iff P).2 hold)
        · exact Or.inl hcodom
      · apply Or.inl
        rintro ⟨x, hx⟩
        have hreach :
            PermReachable P.y.map.face P.y.point (P.yOld x) := by
          apply (hface _ _).1
          simpa [hx] using hzu
        exact PointedHypermap.y_not_faceReachable_point_old P x hreach
      · rcases List.mem_map.mp hz with ⟨x, hx, rfl⟩
        apply Or.inr
        refine Hypermap.FaceBand.of_mem (G := G0) ?_ hzu
        exact List.mem_map.mpr
          ⟨x, List.drop_subset 1 r hx, rfl⟩

/-- Coq `EpH1`: after deleting the six non-original `ecpH` darts, the old
target is the new target together with the face of the removed middle ring
dart.  That extra face is contributed unconditionally by `rqsH`. -/
theorem rqSeqTarget_comp_hOld_iff
    (P : PointedHypermap) {G0 : Hypermap}
    (h : P.h.map.Dart → G0.Dart)
    (hface : ∀ x y : P.h.map.Dart,
      PermReachable G0.face (h x) (h y) ↔
        PermReachable P.h.map.face x y)
    (hproper : P.map.ProperRingHead P.point)
    (hlong : P.map.LongRingHead P.point)
    (r : List P.map.Dart)
    (hr : r = P.map.node P.point :: P.point ::
      P.map.face (P.map.edge P.point) :: r.drop 3)
    (u : G0.Dart) :
    RqSeqTarget (fun x => h (P.hOld x)) r u ↔
      G0.FaceBand [h (P.hOld P.point)] u ∨
        RqSeqTarget h
          (P.h.map.node P.h.point :: P.h.point ::
            (r.drop 2).map P.hOld) u := by
  let a := P.map.face (P.map.edge P.point)
  let nu0 := P.h.map.node P.h.point
  let u0 := P.h.point
  let v1 := P.hOld (P.map.node P.point)
  let v2 := P.hOld P.point
  have hdrop2 : r.drop 2 = a :: r.drop 3 := by
    calc
      r.drop 2 =
          (P.map.node P.point :: P.point :: a :: r.drop 3).drop 2 :=
        congrArg (List.drop 2) (by simpa [a] using hr)
      _ = a :: r.drop 3 := rfl
  have hnu0v1 : PermReachable P.h.map.face nu0 v1 := by
    exact (PointedHypermap.h_faceReachable_node_point_old_iff
      P hproper).2
      (PermReachable.refl P.map.face (P.map.node P.point))
  have hv2OldNewEdge :
      PermReachable P.h.map.face v2
        (ExtDart.old ExtDart.newEdge) := by
    change PermReachable
      (Hypermap.extensionN P.y.map P.y.point).face
      (ExtDart.old (P.yOld P.point))
      (ExtDart.old ExtDart.newEdge)
    exact (Hypermap.extensionN_old_faceReachable_iff
      (G := P.y.map) P.y.point).2
      ((PointedHypermap.yOld_faceReachable_newEdge_iff P).2
        (PermReachable.refl P.map.face P.point))
  have hv3NewEdge :
      PermReachable P.h.map.face (P.hOld a) ExtDart.newEdge := by
    apply PermReachable.symm P.h.map.face
    exact
      (Hypermap.extensionH_faceReachable_newEdge_old_iff_face_edge_of_proper_long
        (G := P.map) P.point hproper hlong).2
        (PermReachable.refl P.map.face a)
  have hnodeEq :
      (ExtDart.old (ExtDart.old ExtDart.newEdge) : P.h.map.Dart) =
        nu0 := by
    change ExtDart.old (ExtDart.old ExtDart.newEdge) =
      (Hypermap.extensionH P.map P.point).node ExtDart.new
    unfold Hypermap.extensionH Hypermap.extensionN
    rw [Hypermap.ExtensionN.node_new,
      if_pos (Hypermap.extensionY_long_new_of_proper
        (G := P.map) P.point hproper),
      Hypermap.extensionY_node_new]
    rfl
  have hfresh (x : P.h.map.Dart)
      (hx : x = ExtDart.new ∨ x = ExtDart.old ExtDart.new ∨
        x = ExtDart.old (ExtDart.old ExtDart.new)) :
      PermReachable P.h.map.face u0 x := by
    exact
      (Hypermap.extensionH_faceReachable_new_iff_three_of_proper
        (G := P.map) P.point hproper).2 hx
  have hnewMemNode :
      h nu0 ∈
        (P.h.map.node P.h.point :: P.h.point ::
          (r.drop 2).map P.hOld).map h := by
    exact List.Mem.head _
  have hnewMemPoint :
      h u0 ∈
        (P.h.map.node P.h.point :: P.h.point ::
          (r.drop 2).map P.hOld).map h := by
    exact List.Mem.tail _ (List.Mem.head _)
  have hnewMemOld {x : P.map.Dart} (hx : x ∈ r.drop 2) :
      h (P.hOld x) ∈
        (P.h.map.node P.h.point :: P.h.point ::
          (r.drop 2).map P.hOld).map h := by
    simp only [List.map_cons, List.mem_cons, List.mem_map]
    exact Or.inr (Or.inr
      ⟨P.hOld x, ⟨x, hx, rfl⟩, rfl⟩)
  constructor
  · rintro (houtside | hband)
    · by_cases houtsideH : ¬ RqSeqCodom h u
      · exact Or.inr (Or.inl houtsideH)
      · rcases Classical.byContradiction houtsideH with ⟨y, rfl⟩
        cases y with
        | new =>
            exact Or.inr (Or.inr
              (Hypermap.FaceBand.of_mem (G := G0) hnewMemPoint
                (PermReachable.refl G0.face (h u0))))
        | newEdge =>
            exact Or.inr (Or.inr
              (Hypermap.FaceBand.of_mem (G := G0)
                (hnewMemOld (by rw [hdrop2]; exact List.Mem.head _))
                ((hface _ _).2 hv3NewEdge)))
        | old y =>
            cases y with
            | new =>
                exact Or.inr (Or.inr
                  (Hypermap.FaceBand.of_mem (G := G0) hnewMemPoint
                    ((hface _ _).2
                      (hfresh _ (Or.inr (Or.inl rfl))))))
            | newEdge =>
                exact Or.inl
                  ((Hypermap.FaceBand.singleton (G := G0)).2
                    ((hface _ _).2 hv2OldNewEdge))
            | old y =>
                cases y with
                | new =>
                    exact Or.inr (Or.inr
                      (Hypermap.FaceBand.of_mem (G := G0) hnewMemPoint
                        ((hface _ _).2
                          (hfresh _ (Or.inr (Or.inr rfl))))))
                | newEdge =>
                    rw [hnodeEq]
                    exact Or.inr (Or.inr
                      (Hypermap.FaceBand.of_mem (G := G0) hnewMemNode
                        (PermReachable.refl G0.face (h nu0))))
                | old x =>
                    exact False.elim (houtside ⟨x, rfl⟩)
    · rcases hband with ⟨z, hz, hzu⟩
      rcases List.mem_map.mp hz with ⟨x, hx, rfl⟩
      rw [hr] at hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inr (Or.inr
          (Hypermap.FaceBand.of_mem (G := G0) hnewMemNode
            (PermReachable.trans G0.face
              ((hface _ _).2 hnu0v1) hzu)))
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact Or.inl
            ((Hypermap.FaceBand.singleton (G := G0)).2 hzu)
        · exact Or.inr (Or.inr
            (Hypermap.FaceBand.of_mem (G := G0)
              (hnewMemOld (by rw [hdrop2]; exact hx)) hzu))
  · rintro (hmiddle | htarget)
    · by_cases hcodom : RqSeqCodom (fun x => h (P.hOld x)) u
      · rcases hcodom with ⟨x, rfl⟩
        apply Or.inr
        refine Hypermap.FaceBand.of_mem (G := G0) ?_
          ((Hypermap.FaceBand.singleton (G := G0)).1 hmiddle)
        apply List.mem_map.mpr
        exact ⟨P.point, by rw [hr]; exact List.Mem.tail _ (List.Mem.head _), rfl⟩
      · exact Or.inl hcodom
    · rcases htarget with houtside | hband
      · exact Or.inl (fun ⟨x, hx⟩ => houtside ⟨P.hOld x, hx⟩)
      · rcases hband with ⟨z, hz, hzu⟩
        rcases List.mem_map.mp hz with ⟨y, hy, rfl⟩
        have hy' : y = nu0 ∨ y = u0 ∨
            y ∈ (r.drop 2).map P.hOld := by
          simpa only [List.mem_cons] using hy
        rcases hy' with rfl | rfl | hyOld
        · by_cases hcodom : RqSeqCodom (fun x => h (P.hOld x)) u
          · rcases hcodom with ⟨x, rfl⟩
            apply Or.inr
            refine Hypermap.FaceBand.of_mem (G := G0)
              (x := h v1) (u := h (P.hOld x)) ?_ ?_
            · exact List.mem_map.mpr
                ⟨P.map.node P.point, by rw [hr]; exact List.Mem.head _, rfl⟩
            · exact PermReachable.trans G0.face
                ((hface _ _).2
                  (PermReachable.symm P.h.map.face hnu0v1)) hzu
          · exact Or.inl hcodom
        · apply Or.inl
          rintro ⟨x, hx⟩
          have hreach :
              PermReachable P.h.map.face u0 (P.hOld x) := by
            apply (hface _ _).1
            simpa [hx] using hzu
          exact PointedHypermap.h_not_faceReachable_point_old P x hreach
        · rcases List.mem_map.mp hyOld with ⟨x, hx, rfl⟩
          apply Or.inr
          refine Hypermap.FaceBand.of_mem (G := G0) ?_ hzu
          exact List.mem_map.mpr
            ⟨x, List.drop_subset 2 r hx, rfl⟩

end CFQuiz

end FourColor

end Schematic.Math.GraphTheory
