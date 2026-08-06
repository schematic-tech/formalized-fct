import FourColorTheorem.FourColor.Configuration.QuizEmbedding.Base

namespace Schematic.Math.GraphTheory.FourColor.Hypermap.ValidQuizFor

universe u

theorem left_tail_eq_of_cons_append_eq
    {α : Type u}
    {a b a' b' : α} {xs xs' ys ys' : List α}
    (h : (a :: xs) ++ (b :: ys) = (a' :: xs') ++ (b' :: ys'))
    (hlen : xs.length = xs'.length) :
    xs = xs' := by
  have ht :=
    congrArg (fun l : List α => (l.drop 1).take xs.length) h
  simpa [hlen] using ht

theorem right_tail_eq_of_cons_append_eq
    {α : Type u}
    {a b a' b' : α} {xs xs' ys ys' : List α}
    (h : (a :: xs) ++ (b :: ys) = (a' :: xs') ++ (b' :: ys'))
    (hlen : xs.length = xs'.length) :
    ys = ys' := by
  have hleft : xs = xs' := left_tail_eq_of_cons_append_eq h hlen
  subst xs'
  have ht : xs ++ b :: ys = xs ++ b' :: ys' := by
    simpa using congrArg List.tail h
  exact (List.cons.inj (List.append_cancel_left ht)).2

theorem append_cons_tails_eq_of_length
    {α : Type u} {b b' : α} {xs xs' ys ys' : List α}
    (h : xs ++ b :: ys = xs' ++ b' :: ys')
    (hlen : xs.length = xs'.length) :
    xs = xs' ∧ b = b' ∧ ys = ys' := by
  have hxs : xs = xs' := by
    have ht := congrArg (fun l : List α => l.take xs.length) h
    simpa [hlen] using ht
  subst xs'
  have ht := congrArg (fun l : List α => l.drop xs.length) h
  simp at ht
  exact ⟨rfl, ht.1, ht.2⟩

end Schematic.Math.GraphTheory.FourColor.Hypermap.ValidQuizFor
