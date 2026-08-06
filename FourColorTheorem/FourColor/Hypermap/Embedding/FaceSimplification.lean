import FourColorTheorem.FourColor.Hypermap.Embedding.RLinkConnectivity

/-! Erasure of repeated face classes from `rlink` paths and cycles. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u

variable {G : Hypermap.{u}}

/-- Coq `simplify_rlink`: erase loops at the level of face orbits while
preserving the endpoint and retaining only darts from the original path. -/
theorem RLinkPath.simplifyFace
    {x : G.Dart} {p : List G.Dart}
    (hp : G.RLinkPath x p) :
    ∃ q : List G.Dart,
      G.RLinkPath x q ∧
        G.FaceSimple q ∧
          (x :: q).getLastD x = (x :: p).getLastD x ∧
            (p = [] ↔ q = []) ∧
              ∀ y : G.Dart, y ∈ q → y ∈ p := by
  classical
  let P : Nat → Prop := fun n =>
    ∀ {x : G.Dart} {p : List G.Dart},
      p.length = n → G.RLinkPath x p →
        ∃ q : List G.Dart,
          G.RLinkPath x q ∧
            G.FaceSimple q ∧
              (x :: q).getLastD x = (x :: p).getLastD x ∧
                (p = [] ↔ q = []) ∧
                  ∀ y : G.Dart, y ∈ q → y ∈ p
  have hP : ∀ n : Nat, (∀ m : Nat, m < n → P m) → P n := by
    intro n ih x p hlen hp
    cases p with
    | nil =>
        exact ⟨[], by simp [RLinkPath], by simp [FaceSimple],
          by simp [List.getLastD], by simp, by simp⟩
    | cons y p =>
        have hp' : G.RLink x y ∧ G.RLinkPath y p := by
          simpa [RLinkPath] using hp
        by_cases hyBand : G.FaceBand p y
        · rcases hyBand with ⟨z, hz, hzy⟩
          rcases (List.mem_iff_append).1 hz with ⟨pre, post, hsplit⟩
          have htail : G.RLinkPath y (pre ++ z :: post) := by
            simpa [hsplit] using hp'.2
          have hzpost : G.RLinkPath z post :=
            RLinkPath.suffix_of_append_cons (G := G) htail
          have hxz : G.RLink x z :=
            RLink.of_faceReachable_right (G := G) hp'.1
              (PermReachable.symm G.face hzy)
          have hxshort : G.RLinkPath x (z :: post) := ⟨hxz, hzpost⟩
          have hlt : (z :: post).length < n := by
            have hlen' : (y :: (pre ++ z :: post)).length = n := by
              simpa [hsplit] using hlen
            simp only [List.length_cons, List.length_append] at hlen' ⊢
            omega
          rcases ih (z :: post).length hlt rfl hxshort with
            ⟨q, hq, hsimple, hlast, hnil, hsub⟩
          refine ⟨q, hq, hsimple, ?_, ?_, ?_⟩
          · calc
              (x :: q).getLastD x =
                  (x :: z :: post).getLastD x := hlast
              _ = (x :: y :: p).getLastD x := by
                    simp [hsplit, List.getLastD]
          · constructor
            · intro h
              cases h
            · intro hqnil
              have : z :: post = [] := hnil.mpr hqnil
              cases this
          · intro w hw
            have hwShort : w ∈ z :: post := hsub w hw
            simp only [List.mem_cons] at hwShort ⊢
            rcases hwShort with rfl | hwPost
            · exact Or.inr (by rw [hsplit]; simp)
            · exact Or.inr (by
                rw [hsplit]
                exact List.mem_append_right pre (List.mem_cons_of_mem z hwPost))
        · have hlt : p.length < n := by
            simp only [List.length_cons] at hlen
            omega
          rcases ih p.length hlt rfl hp'.2 with
            ⟨q, hq, hsimple, hlast, hnil, hsub⟩
          refine ⟨y :: q, ⟨hp'.1, hq⟩, ?_, ?_, ?_, ?_⟩
          · rw [FaceSimple, List.pairwise_cons]
            refine ⟨?_, hsimple⟩
            intro z hz hyz
            apply hyBand
            exact ⟨z, hsub z hz, PermReachable.symm G.face hyz⟩
          · simpa [List.getLastD] using hlast
          · simp
          · intro z hz
            simp only [List.mem_cons] at hz ⊢
            rcases hz with rfl | hz
            · exact Or.inl rfl
            · exact Or.inr (hsub z hz)
  exact (Nat.strong_induction_on (p := P) p.length hP) rfl hp

/-- Closed-path form of Coq `simplify_rlink`: keep a prescribed head and erase
face repetitions until a simple `rlink` cycle remains.  Every retained tail
dart comes from the original closed path. -/
theorem RLinkCycle.simplifyFaceAtHead
    {x : G.Dart} {p : List G.Dart}
    (hp : G.RLinkCycle (x :: p)) :
    ∃ q : List G.Dart,
      G.SimpleRLinkCycle (x :: q) ∧
        ∀ z : G.Dart, z ∈ q → z ∈ p := by
  classical
  rcases RLinkPath.simplifyFace (G := G) hp.path with
    ⟨q, hpath, hsimple, hlast, _hnil, hsub⟩
  have hclosing : G.RLink ((x :: q).getLastD x) x := by
    rw [hlast]
    exact hp.closing
  by_cases hhead : ∀ z : G.Dart, z ∈ q →
      ¬ PermReachable G.face x z
  · refine ⟨q, ⟨⟨hpath, hclosing⟩, ?_⟩, hsub⟩
    rw [FaceSimple, List.pairwise_cons]
    exact ⟨hhead, hsimple⟩
  · simp only [not_forall, not_not] at hhead
    rcases hhead with ⟨y, hyq, hxy⟩
    rcases List.eq_append_cons_of_mem hyq with
      ⟨pre, post, hq, hyNotPre⟩
    have hpath' : G.RLinkPath x (pre ++ y :: post) := by
      simpa [hq] using hpath
    have hprefix : G.RLinkPath x pre :=
      RLinkPath.prefix_of_append (G := G) hpath'
    have hlastLink : G.RLink ((x :: pre).getLastD x) y :=
      RLinkPath.last_link_of_append_cons (G := G) hpath'
    have hclose : G.RLink ((x :: pre).getLastD x) x :=
      RLink.of_faceReachable_right (G := G) hlastLink
        (PermReachable.symm G.face hxy)
    have hpreSimple : G.FaceSimple pre := by
      rw [FaceSimple] at hsimple ⊢
      have hpreSub : pre.Sublist q := by
        rw [hq]
        exact List.sublist_append_left pre (y :: post)
      exact List.Pairwise.sublist hpreSub hsimple
    have hheadPre : ∀ z : G.Dart, z ∈ pre →
        ¬ PermReachable G.face x z := by
      intro z hz hxz
      have hzq : z ∈ q := by rw [hq]; simp [hz]
      have hyq' : y ∈ q := by rw [hq]; simp
      have hzy : PermReachable G.face z y :=
        PermReachable.trans G.face
          (PermReachable.symm G.face hxz) hxy
      have hEq : z = y :=
        FaceSimple.eq_of_faceReachable_of_mem
          (G := G) hsimple hzq hyq' hzy
      exact hyNotPre (hEq ▸ hz)
    refine ⟨pre, ⟨⟨hprefix, hclose⟩, ?_⟩, ?_⟩
    · rw [FaceSimple, List.pairwise_cons]
      exact ⟨hheadPre, hpreSimple⟩
    · intro z hz
      apply hsub z
      rw [hq]
      exact List.mem_append_left (y :: post) hz

/-- Coq's `find (cface x) p` construction without executable-index
bookkeeping.  Split a closed `rlink` path immediately before its first tail
dart in the head face; the retained contiguous prefix forms a simple cycle. -/
theorem RLinkCycle.firstFaceSimplePrefix
    {x : G.Dart} {p : List G.Dart}
    (hcycle : G.RLinkCycle (x :: p))
    (hpSimple : G.FaceSimple p) :
    ∃ pre post : List G.Dart,
      p = pre ++ post ∧
        G.SimpleRLinkCycle (x :: pre) ∧
          (∀ z : G.Dart, z ∈ pre →
            ¬ PermReachable G.face x z) ∧
            (post = [] ∨
              ∃ y ys, post = y :: ys ∧
                PermReachable G.face x y) := by
  classical
  have hsplitAux : ∀ s : List G.Dart,
      ∃ pre post : List G.Dart,
        s = pre ++ post ∧
          (∀ z : G.Dart, z ∈ pre →
            ¬ PermReachable G.face x z) ∧
            (post = [] ∨
              ∃ y ys, post = y :: ys ∧
                PermReachable G.face x y) := by
    intro s
    induction s with
    | nil =>
        exact ⟨[], [], by simp, by simp⟩
    | cons y ys ih =>
        by_cases hxy : PermReachable G.face x y
        · exact ⟨[], y :: ys, by simp, by simp [hxy]⟩
        · rcases ih with ⟨pre, post, hys, havoid, hpost⟩
          refine ⟨y :: pre, post, ?_, ?_, hpost⟩
          · simp [hys]
          · intro z hz
            rcases List.mem_cons.mp hz with rfl | hz
            · exact hxy
            · exact havoid z hz
  have hsplit := hsplitAux p
  rcases hsplit with ⟨pre, post, hp, havoid, hpost⟩
  have hpath : G.RLinkPath x pre := by
    apply RLinkPath.prefix_of_append (G := G)
    simpa [hp] using hcycle.path
  have hclose : G.RLink ((x :: pre).getLastD x) x := by
    rcases hpost with hnil | ⟨y, ys, hpost, hxy⟩
    · subst post
      simpa [hp] using hcycle.closing
    · subst post
      have hpathFull : G.RLinkPath x (pre ++ y :: ys) := by
        simpa [hp] using hcycle.path
      exact RLink.of_faceReachable_right (G := G)
        (RLinkPath.last_link_of_append_cons (G := G) hpathFull)
        (PermReachable.symm G.face hxy)
  have hpreSimple : G.FaceSimple pre := by
    rw [FaceSimple] at hpSimple ⊢
    apply List.Pairwise.sublist (List.sublist_append_left pre post)
    simpa [hp] using hpSimple
  have hfullSimple : G.FaceSimple (x :: pre) := by
    rw [FaceSimple, List.pairwise_cons]
    exact ⟨havoid, hpreSimple⟩
  exact ⟨pre, post, hp, ⟨⟨hpath, hclose⟩, hfullSimple⟩,
    havoid, hpost⟩

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
