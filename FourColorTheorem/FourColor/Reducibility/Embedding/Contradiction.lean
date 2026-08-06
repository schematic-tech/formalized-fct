import FourColorTheorem.FourColor.Reducibility.Embedding.Cotrace

/-! The reducibility contradiction for an embedded configuration. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u

namespace Embeddable

variable {G : Hypermap.{u}} {r : List G.Dart}

/-- An ordinary source coloring restricts to the explicit embedded disk. -/
theorem embeddedDisk_coloring
    (hG : G.Embeddable r) {k : G.Dart -> Color}
    (hk : G.Coloring k) :
    (embeddedDisk hG).Coloring (k ∘ embeddedDiskVal hG) := by
  constructor
  · intro x hsame
    have hsame' := hsame
    rw [Function.comp_apply, Function.comp_apply,
      embeddedDisk_edge_val] at hsame'
    split at hsame'
    · exact hk.1 _ hsame'
    · have hreach : PermReachable G.face
          (G.edge (embeddedDiskVal hG x))
          (G.edge (G.node (G.edge (embeddedDiskVal hG x)))) := by
        rw [Hypermap.edge_node_eq_face_symm]
        exact PermReachable.backward G.face _
      have heq := Coloring.eq_of_face_reachable (G := G) hk hreach
      exact hk.1 _ (heq.symm.trans hsame')
  · intro x
    exact Coloring.eq_of_face_reachable (G := G) hk
      (embeddedDisk_faceReachable_map hG
        (PermReachable.forward (embeddedDisk hG).face x))

/-- The source reversed-perimeter trace is read in reverse on the crossed disk
boundary, exactly as in the last block of Coq `not_embed_reducible`. -/
theorem embeddedDisk_ringTrace_of_source_reverse
    (hG : G.Embeddable r) {et : ColSeq}
    (htrace : G.RingTrace r.reverse et) :
    (embeddedDisk hG).RingTrace (embeddedDiskBoundary hG) et.reverse := by
  classical
  rcases htrace with ⟨k, hk, het⟩
  let f : G.Dart -> Color := fun x => k (G.edge x)
  have hfg : ∀ x : G.Dart, f (G.node x) = k x := by
    intro x
    have hreach : PermReachable G.face (G.edge (G.node x)) x := by
      rw [Hypermap.edge_node_eq_face_symm]
      simpa using PermReachable.forward G.face (G.face.symm x)
    exact (Coloring.eq_of_face_reachable (G := G) hk hreach).symm
  have hrotateColors : (r.map f).rotate 1 = r.map k := by
    calc
      (r.map f).rotate 1 = (r.rotate 1).map f := by
        rw [List.map_rotate]
      _ = (r.map G.node).map f := by
        rw [functionCycleMap_eq_rotate_one hG.cycle]
      _ = r.map k := by
        simp only [List.map_map]
        apply List.map_congr_left
        intro x hx
        exact hfg x
  have hcolors :
      (embeddedDisk hG).colorsOn (k ∘ embeddedDiskVal hG)
          (embeddedDiskBoundary hG) = r.map f := by
    have hmap :
        ((embeddedDiskBoundary hG).map (embeddedDiskVal hG)).map k =
          (G.RevRing r.reverse).map k :=
      congrArg (List.map k) (map_embeddedDiskBoundary hG)
    calc
      (embeddedDisk hG).colorsOn (k ∘ embeddedDiskVal hG)
          (embeddedDiskBoundary hG) =
          ((embeddedDiskBoundary hG).map (embeddedDiskVal hG)).map k := by
            unfold Hypermap.colorsOn
            rw [List.map_map]
      _ = (G.RevRing r.reverse).map k := hmap
      _ = r.map f := by
        simp [RevRing, List.map_map, f]
  have hrightRotate : r.map f = rotateRightOne (r.map k) := by
    cases r with
    | nil => simp [rotateRightOne]
    | cons x xs =>
        have hne : (List.map f (x :: xs)) ≠ [] := by simp
        have hundo := rotateRightOne_rotate_one_of_ne_nil hne
        rw [hrotateColors] at hundo
        exact hundo.symm
  refine ⟨k ∘ embeddedDiskVal hG, hG.embeddedDisk_coloring hk, ?_⟩
  calc
    et.reverse =
        (ColSeq.trace (G.colorsOn k r.reverse)).reverse :=
      congrArg List.reverse het
    _ = (ColSeq.trace (r.map k).reverse).reverse := by
      simp [Hypermap.colorsOn, List.map_reverse]
    _ = ColSeq.trace (rotateRightOne (r.map k)) :=
      (trace_rotateRightOne_eq_trace_reverse_reverse (r.map k)).symm
    _ = ColSeq.trace (r.map f) := by rw [hrightRotate]
    _ = ColSeq.trace ((embeddedDisk hG).colorsOn
        (k ∘ embeddedDiskVal hG) (embeddedDiskBoundary hG)) := by
      rw [hcolors]

/-- Coq `not_embed_reducible`: a reducible embedded configuration contradicts
minimal non-colorability. -/
theorem not_embed_reducible
    {H : Hypermap.{u}} {h : G.Dart -> H.Dart}
    (hG : G.Embeddable r) (hH : H.MinimalCounterexample)
    (hembed : Preembedding G H (G.Kernel r) h)
    {cc : Finset G.Dart} (hred : G.CReducible r cc) : False := by
  rcases hG.embed_contract hH hembed hred.valid with
    ⟨et, hcontractTrace, hremTrace⟩
  have hcoclosure : Chromogram.KempeCoclosure
      (G.RingTrace r.reverse) et :=
    CReducible.contract_trace_coclosure (G := G) hred hcontractTrace
  rcases hcoclosure.closed_meets
      (hG.embed_closure hH hembed) hremTrace with
    ⟨et', hsourceTrace, hremCotrace⟩
  have hdiskTrace : (embeddedDisk hG).RingTrace
      (embeddedDiskBoundary hG) et'.reverse :=
    hG.embeddedDisk_ringTrace_of_source_reverse hsourceTrace
  have hremRot := RingTrace.rotate_one
    (G := embeddedRemainder hG hH hembed) hremCotrace
  have hboundary :
      (rotateRightOne (embeddedRemainderBoundary hG hH hembed)).rotate 1 =
        embeddedRemainderBoundary hG hH hembed := by
    change (listUnrot1
      (embeddedRemainderBoundary hG hH hembed)).rotate 1 = _
    exact list_rotate_one_unrot1 _
  rw [hboundary] at hremRot
  have hcolorable : H.FourColorable :=
    (hG.embeddingPatch hH hembed).colorable_patch.mpr
      ⟨et'.reverse, hdiskTrace, by simpa using hremRot⟩
  exact hH.noncolorable hcolorable

end Embeddable

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
