import FourColorTheorem.FourColor.Reducibility.KernelCertificate.IndexedReplay

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

def config164Stage005Count : Nat := 12

def config164Stage005Length : Nat := 7

set_option maxRecDepth 100000 in
def config164Stage005Tree : NatTree :=
  NatTree.node 6 (NatTree.node 3 (NatTree.node 1 (NatTree.leaf 21) (NatTree.node 1 (NatTree.leaf 129) (NatTree.leaf 237))) (NatTree.node 1 (NatTree.leaf 19) (NatTree.node 1 (NatTree.leaf 127) (NatTree.leaf 235)))) (NatTree.node 3 (NatTree.node 1 (NatTree.leaf 1483) (NatTree.node 1 (NatTree.leaf 1591) (NatTree.leaf 1699))) (NatTree.node 1 (NatTree.leaf 1481) (NatTree.node 1 (NatTree.leaf 1589) (NatTree.leaf 1697))))

def config164Stage005Source : SourceTable := config164Stage005Tree.get

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
