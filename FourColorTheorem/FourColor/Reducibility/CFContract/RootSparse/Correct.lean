import FourColorTheorem.FourColor.Reducibility.CFContract.RootSparse.Y
import FourColorTheorem.FourColor.Reducibility.CFContract.RootSparse.Initial
import FourColorTheorem.FourColor.Reducibility.CFContract.RootSparse.H
import FourColorTheorem.FourColor.Reducibility.CFContract.Program.Induction

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace PointedHypermap

/-- Coq `sparse_cfctr`: every successful contracted program selects a sparse
rooted set in the original configuration map. -/
theorem rootSparse_contractProgram
    {mr mc : List Bool} {cp cpc : CProg}
    (hmr : mr.length = CProg.ringSize cp)
    (hmc : mc.length = CProg.contractEdgeSize cp)
    (hrun : CProg.contractProgram mr mc cp = some cpc) :
    RootSparse (cpmap cp) (cpSparseTail mr mc cp) := by
  apply CFContract.Internal.contractProgram_induction
    (P := fun mr mc cp _ => RootSparse (cpmap cp) (cpSparseTail mr mc cp))
  · intro n mr mc cp cpc hmr _ hrun hrec
    exact rootSparse_rotate (CProg.contractProgram_config hrun)
      (by simpa [CProg.ringSize] using hmr) hrec
  · intro b1 b2 b3 hnsp
    exact rootSparse_contractProgram_y_nil
      (mr := [b1, b2, b3]) (mc := [])
      (cpc := CFContract.Internal.yNilResult b1 b2 b3)
      (by simp [CProg.ringSize]) (by simp [CProg.contractEdgeSize])
      (by simp [CProg.contractProgram, hnsp, CFContract.Internal.yNilResult])
  · intro b1 b2 b3 mr mc step cp cpc _ _ hnsp hrun hrec
    exact rootSparse_y_step b1 b2 b3
      (CProg.contractProgram_config hrun) hnsp hrec
  · intro b1 b2 b3 b4 b5 mr mc cp cpc _ _ hnspL hnspR _ hrun hrec
    exact rootSparse_h_step b1 b2 b3 b4 b5
      (CProg.contractProgram_config hrun) hnspL hnspR hrec
  all_goals assumption


end PointedHypermap

end FourColor

end Schematic.Math.GraphTheory
