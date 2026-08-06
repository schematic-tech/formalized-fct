import FourColorTheorem.FourColor.Reducibility.KernelCertificate.IndexedReplay

namespace Schematic.Math.GraphTheory.FourColor.KernelCertificate

def config164Stage008Count : Nat := 48

def config164Stage008Length : Nat := 9

set_option maxRecDepth 100000 in
def config164Stage008Tree : NatTree :=
  NatTree.node 24 (NatTree.node 12 (NatTree.node 6 (NatTree.node 3 (NatTree.node 1 (NatTree.leaf 57) (NatTree.node 1 (NatTree.leaf 17553) (NatTree.leaf 381))) (NatTree.node 1 (NatTree.leaf 17877) (NatTree.node 1 (NatTree.leaf 705) (NatTree.leaf 18201)))) (NatTree.node 3 (NatTree.node 1 (NatTree.leaf 6627) (NatTree.node 1 (NatTree.leaf 6951) (NatTree.leaf 7275))) (NatTree.node 1 (NatTree.leaf 10995) (NatTree.node 1 (NatTree.leaf 11319) (NatTree.leaf 11643))))) (NatTree.node 6 (NatTree.node 3 (NatTree.node 1 (NatTree.leaf 6639) (NatTree.node 1 (NatTree.leaf 6963) (NatTree.leaf 7287))) (NatTree.node 1 (NatTree.leaf 55) (NatTree.node 1 (NatTree.leaf 17551) (NatTree.leaf 379)))) (NatTree.node 3 (NatTree.node 1 (NatTree.leaf 17875) (NatTree.node 1 (NatTree.leaf 703) (NatTree.leaf 18199))) (NatTree.node 1 (NatTree.leaf 6625) (NatTree.node 1 (NatTree.leaf 6949) (NatTree.leaf 7273)))))) (NatTree.node 12 (NatTree.node 6 (NatTree.node 3 (NatTree.node 1 (NatTree.leaf 11005) (NatTree.node 1 (NatTree.leaf 11329) (NatTree.leaf 11653))) (NatTree.node 1 (NatTree.leaf 79) (NatTree.node 1 (NatTree.leaf 17575) (NatTree.leaf 403)))) (NatTree.node 3 (NatTree.node 1 (NatTree.leaf 17899) (NatTree.node 1 (NatTree.leaf 727) (NatTree.leaf 18223))) (NatTree.node 1 (NatTree.leaf 10991) (NatTree.node 1 (NatTree.leaf 11315) (NatTree.leaf 11639))))) (NatTree.node 6 (NatTree.node 3 (NatTree.node 1 (NatTree.leaf 6635) (NatTree.node 1 (NatTree.leaf 6959) (NatTree.leaf 7283))) (NatTree.node 1 (NatTree.leaf 11003) (NatTree.node 1 (NatTree.leaf 11327) (NatTree.leaf 11651)))) (NatTree.node 3 (NatTree.node 1 (NatTree.leaf 77) (NatTree.node 1 (NatTree.leaf 17573) (NatTree.leaf 401))) (NatTree.node 1 (NatTree.leaf 17897) (NatTree.node 1 (NatTree.leaf 725) (NatTree.leaf 18221))))))

def config164Stage008Source : SourceTable := config164Stage008Tree.get

end Schematic.Math.GraphTheory.FourColor.KernelCertificate
