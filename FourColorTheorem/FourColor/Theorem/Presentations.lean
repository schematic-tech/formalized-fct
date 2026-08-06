import FourColorTheorem.FourColor.Theorem.Combinatorial
import FourColorTheorem.FourColor.Presentation.Generated.Present5
import FourColorTheorem.FourColor.Presentation.Generated.Present6
import FourColorTheorem.FourColor.Presentation.Generated.Present7
import FourColorTheorem.FourColor.Presentation.Generated.Present8
import FourColorTheorem.FourColor.Presentation.Generated.Present9
import FourColorTheorem.FourColor.Presentation.Generated.Present10
import FourColorTheorem.FourColor.Presentation.Generated.Present11

/-!
Bridge from the mechanically ported presentation scripts into the
combinatorial four-colour theorem layer.

This module intentionally imports the large generated `Present7`, `Present8`,
and `Present9` proofs.  It is kept out of the default `FourColorTheorem.FourColor`
aggregate while lower semantic dependencies are still changing, so routine
proof-development builds do not re-elaborate the large presentation scripts.
-/

namespace Schematic.Math.GraphTheory




namespace FourColor

namespace CombinatorialFourColor

universe u

noncomputable section

theorem noMinimalCounterexample_of_redpartPresent5AndPresentations
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshortNode : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u})
    (hvalid : Presentation.MirrorValidHubTransport.{u})
    (hfitMirror : Presentation.MirrorExactFitTransport.{u})
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11)) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_redpartAndPresentations
    hconnected hshortNode heven hshortFace
    hredCert hredpart
    (PresentationScripts.present5
      (Unavoidability.cubicMinimalCounterexamples_of_noShortNodeOrbits
        hshortNode)
      (Unavoidability.pentagonalMinimalCounterexamples_of_noShortFaceOrbits
        hshortFace)
      hredpart hvalid hfitMirror)
    h6 h7 h8 h9 h10 h11

theorem hypermapFourColor_of_redpartPresent5AndPresentations
    (hredMin : MinimalCounterexampleReduction.{u})
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshortNode : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u})
    (hvalid : Presentation.MirrorValidHubTransport.{u})
    (hfitMirror : Presentation.MirrorExactFitTransport.{u})
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11)) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample hredMin
    (noMinimalCounterexample_of_redpartPresent5AndPresentations
      hconnected hshortNode heven hshortFace
      hredCert hredpart hvalid hfitMirror
      h6 h7 h8 h9 h10 h11)

theorem noMinimalCounterexample_of_redpartPresent5Present6AndPresentations
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshortNode : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u})
    (hvalid : Presentation.MirrorValidHubTransport.{u})
    (hfitMirror : Presentation.MirrorExactFitTransport.{u})
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11)) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_redpartPresent5AndPresentations
    hconnected hshortNode heven hshortFace
    hredCert hredpart hvalid hfitMirror
    (PresentationScripts.present6
      (Unavoidability.cubicMinimalCounterexamples_of_noShortNodeOrbits
        hshortNode)
      (Unavoidability.pentagonalMinimalCounterexamples_of_noShortFaceOrbits
        hshortFace)
      hredpart hvalid hfitMirror)
    h7 h8 h9 h10 h11

theorem hypermapFourColor_of_redpartPresent5Present6AndPresentations
    (hredMin : MinimalCounterexampleReduction.{u})
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshortNode : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u})
    (hvalid : Presentation.MirrorValidHubTransport.{u})
    (hfitMirror : Presentation.MirrorExactFitTransport.{u})
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11)) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample hredMin
    (noMinimalCounterexample_of_redpartPresent5Present6AndPresentations
      hconnected hshortNode heven hshortFace
      hredCert hredpart hvalid hfitMirror
      h7 h8 h9 h10 h11)

theorem noMinimalCounterexample_of_redpartPresent5Present6Present11AndPresentations
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshortNode : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u})
    (hvalid : Presentation.MirrorValidHubTransport.{u})
    (hfitMirror : Presentation.MirrorExactFitTransport.{u})
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10)) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_redpartPresent5Present6AndPresentations
    hconnected hshortNode heven hshortFace
    hredCert hredpart hvalid hfitMirror
    h7 h8 h9 h10
    (PresentationScripts.present11
      (Unavoidability.cubicMinimalCounterexamples_of_noShortNodeOrbits
        hshortNode)
      (Unavoidability.pentagonalMinimalCounterexamples_of_noShortFaceOrbits
        hshortFace)
      hredpart hvalid hfitMirror)

theorem hypermapFourColor_of_redpartPresent5Present6Present11AndPresentations
    (hredMin : MinimalCounterexampleReduction.{u})
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshortNode : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u})
    (hvalid : Presentation.MirrorValidHubTransport.{u})
    (hfitMirror : Presentation.MirrorExactFitTransport.{u})
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10)) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample hredMin
    (noMinimalCounterexample_of_redpartPresent5Present6Present11AndPresentations
      hconnected hshortNode heven hshortFace
      hredCert hredpart hvalid hfitMirror
      h7 h8 h9 h10)

theorem noMinimalCounterexample_of_redpartPresent5Present6Present10Present11AndPresentations
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshortNode : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u})
    (hvalid : Presentation.MirrorValidHubTransport.{u})
    (hfitMirror : Presentation.MirrorExactFitTransport.{u})
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9)) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_redpartPresent5Present6Present11AndPresentations
    hconnected hshortNode heven hshortFace
    hredCert hredpart hvalid hfitMirror
    h7 h8 h9
    (PresentationScripts.present10
      (Unavoidability.cubicMinimalCounterexamples_of_noShortNodeOrbits
        hshortNode)
      (Unavoidability.pentagonalMinimalCounterexamples_of_noShortFaceOrbits
        hshortFace)
      hredpart hvalid hfitMirror)

theorem hypermapFourColor_of_redpartPresent5Present6Present10Present11AndPresentations
    (hredMin : MinimalCounterexampleReduction.{u})
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshortNode : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u})
    (hvalid : Presentation.MirrorValidHubTransport.{u})
    (hfitMirror : Presentation.MirrorExactFitTransport.{u})
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9)) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample hredMin
    (noMinimalCounterexample_of_redpartPresent5Present6Present10Present11AndPresentations
      hconnected hshortNode heven hshortFace
      hredCert hredpart hvalid hfitMirror
      h7 h8 h9)

theorem noMinimalCounterexample_of_redpartPresent5Present6Present9Present10Present11AndPresentations
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshortNode : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u})
    (hvalid : Presentation.MirrorValidHubTransport.{u})
    (hfitMirror : Presentation.MirrorExactFitTransport.{u})
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8)) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_redpartPresent5Present6Present10Present11AndPresentations
    hconnected hshortNode heven hshortFace
    hredCert hredpart hvalid hfitMirror
    h7 h8
    (PresentationScripts.present9
      (Unavoidability.cubicMinimalCounterexamples_of_noShortNodeOrbits
        hshortNode)
      (Unavoidability.pentagonalMinimalCounterexamples_of_noShortFaceOrbits
        hshortFace)
      hredpart hvalid hfitMirror)

theorem hypermapFourColor_of_redpartPresent5Present6Present9Present10Present11AndPresentations
    (hredMin : MinimalCounterexampleReduction.{u})
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshortNode : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u})
    (hvalid : Presentation.MirrorValidHubTransport.{u})
    (hfitMirror : Presentation.MirrorExactFitTransport.{u})
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8)) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample hredMin
    (noMinimalCounterexample_of_redpartPresent5Present6Present9Present10Present11AndPresentations
      hconnected hshortNode heven hshortFace
      hredCert hredpart hvalid hfitMirror
      h7 h8)

theorem noMinimalCounterexample_of_redpartPresent5Present6Present8Present9Present10Present11AndPresentations
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshortNode : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u})
    (hvalid : Presentation.MirrorValidHubTransport.{u})
    (hfitMirror : Presentation.MirrorExactFitTransport.{u})
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7)) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_redpartPresent5Present6Present9Present10Present11AndPresentations
    hconnected hshortNode heven hshortFace
    hredCert hredpart hvalid hfitMirror
    h7
    (PresentationScripts.present8
      (Unavoidability.cubicMinimalCounterexamples_of_noShortNodeOrbits
        hshortNode)
      (Unavoidability.pentagonalMinimalCounterexamples_of_noShortFaceOrbits
        hshortFace)
      hredpart hvalid hfitMirror)

theorem hypermapFourColor_of_redpartPresent5Present6Present8Present9Present10Present11AndPresentations
    (hredMin : MinimalCounterexampleReduction.{u})
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshortNode : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u})
    (hvalid : Presentation.MirrorValidHubTransport.{u})
    (hfitMirror : Presentation.MirrorExactFitTransport.{u})
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7)) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample hredMin
    (noMinimalCounterexample_of_redpartPresent5Present6Present8Present9Present10Present11AndPresentations
      hconnected hshortNode heven hshortFace
      hredCert hredpart hvalid hfitMirror
      h7)

theorem noMinimalCounterexample_of_redpartAllPresentations
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshortNode : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u})
    (hvalid : Presentation.MirrorValidHubTransport.{u})
    (hfitMirror : Presentation.MirrorExactFitTransport.{u}) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_redpartPresent5Present6Present8Present9Present10Present11AndPresentations
    hconnected hshortNode heven hshortFace
    hredCert hredpart hvalid hfitMirror
    (PresentationScripts.present7
      (Unavoidability.cubicMinimalCounterexamples_of_noShortNodeOrbits
        hshortNode)
      (Unavoidability.pentagonalMinimalCounterexamples_of_noShortFaceOrbits
        hshortFace)
      hredpart hvalid hfitMirror)

theorem hypermapFourColor_of_redpartAllPresentations
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshortNode : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u})
    (hvalid : Presentation.MirrorValidHubTransport.{u})
    (hfitMirror : Presentation.MirrorExactFitTransport.{u}) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample_reduction
    (noMinimalCounterexample_of_redpartAllPresentations
      hconnected hshortNode heven hshortFace
      hredCert hredpart hvalid hfitMirror)

theorem noMinimalCounterexample_of_redpartAllPresentations_upToEleven
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshortNode : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u})
    (hvalid : Presentation.MirrorValidHubTransport.{u})
    (hfitMirror : Presentation.MirrorExactFitTransportUpTo.{u} 11) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_redpartAndPresentations
    hconnected hshortNode heven hshortFace
    hredCert hredpart
    (PresentationScripts.present5UpTo
      (Unavoidability.cubicMinimalCounterexamples_of_noShortNodeOrbits
        hshortNode)
      (Unavoidability.pentagonalMinimalCounterexamples_of_noShortFaceOrbits
        hshortFace)
      hredpart hvalid
      (Presentation.mirrorExactFitTransportUpTo_mono
        (by omega : 5 ≤ 11) hfitMirror))
    (PresentationScripts.present6UpTo
      (Unavoidability.cubicMinimalCounterexamples_of_noShortNodeOrbits
        hshortNode)
      (Unavoidability.pentagonalMinimalCounterexamples_of_noShortFaceOrbits
        hshortFace)
      hredpart hvalid
      (Presentation.mirrorExactFitTransportUpTo_mono
        (by omega : 6 ≤ 11) hfitMirror))
    (PresentationScripts.present7UpTo
      (Unavoidability.cubicMinimalCounterexamples_of_noShortNodeOrbits
        hshortNode)
      (Unavoidability.pentagonalMinimalCounterexamples_of_noShortFaceOrbits
        hshortFace)
      hredpart hvalid
      (Presentation.mirrorExactFitTransportUpTo_mono
        (by omega : 7 ≤ 11) hfitMirror))
    (PresentationScripts.present8UpTo
      (Unavoidability.cubicMinimalCounterexamples_of_noShortNodeOrbits
        hshortNode)
      (Unavoidability.pentagonalMinimalCounterexamples_of_noShortFaceOrbits
        hshortFace)
      hredpart hvalid
      (Presentation.mirrorExactFitTransportUpTo_mono
        (by omega : 8 ≤ 11) hfitMirror))
    (PresentationScripts.present9UpTo
      (Unavoidability.cubicMinimalCounterexamples_of_noShortNodeOrbits
        hshortNode)
      (Unavoidability.pentagonalMinimalCounterexamples_of_noShortFaceOrbits
        hshortFace)
      hredpart hvalid
      (Presentation.mirrorExactFitTransportUpTo_mono
        (by omega : 9 ≤ 11) hfitMirror))
    (PresentationScripts.present10UpTo
      (Unavoidability.cubicMinimalCounterexamples_of_noShortNodeOrbits
        hshortNode)
      (Unavoidability.pentagonalMinimalCounterexamples_of_noShortFaceOrbits
        hshortFace)
      hredpart hvalid
      (Presentation.mirrorExactFitTransportUpTo_mono
        (by omega : 10 ≤ 11) hfitMirror))
    (PresentationScripts.present11UpTo
      (Unavoidability.cubicMinimalCounterexamples_of_noShortNodeOrbits
        hshortNode)
      (Unavoidability.pentagonalMinimalCounterexamples_of_noShortFaceOrbits
        hshortFace)
      hredpart hvalid hfitMirror)

theorem hypermapFourColor_of_redpartAllPresentations_upToEleven
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshortNode : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u})
    (hvalid : Presentation.MirrorValidHubTransport.{u})
    (hfitMirror : Presentation.MirrorExactFitTransportUpTo.{u} 11) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample_reduction
    (noMinimalCounterexample_of_redpartAllPresentations_upToEleven
      hconnected hshortNode heven hshortFace
      hredCert hredpart hvalid hfitMirror)

theorem noMinimalCounterexample_of_redpartAllPresentations_localMirror
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshortNode : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u})
    (hscore2 : Presentation.MirrorDscore2Transport.{u})
    (hfit : Presentation.MirrorFitTransport.{u}) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_redpartAllPresentations
    hconnected hshortNode heven hshortFace
    hredCert hredpart
    (Presentation.mirrorValidHubTransport_of_dscore2_mirror hscore2)
    (Presentation.mirrorExactFitTransport_of_fit_mirror hfit)

theorem hypermapFourColor_of_redpartAllPresentations_localMirror
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshortNode : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u})
    (hscore2 : Presentation.MirrorDscore2Transport.{u})
    (hfit : Presentation.MirrorFitTransport.{u}) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample_reduction
    (noMinimalCounterexample_of_redpartAllPresentations_localMirror
      hconnected hshortNode heven hshortFace
      hredCert hredpart hscore2 hfit)

theorem noMinimalCounterexample_of_redpartAllPresentations_plainCubicMirror
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshortNode : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u})
    (hfit : Presentation.PlainCubicFitpMirror.{u}) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_redpartAllPresentations
    hconnected hshortNode heven hshortFace
    hredCert hredpart
    (Unavoidability.mirrorValidHubTransport_of_noShortNodeOrbits hshortNode)
    (Presentation.mirrorExactFitTransport_of_plainCubic_fitp_mirror
      (Unavoidability.cubicMinimalCounterexamples_of_noShortNodeOrbits
        hshortNode)
      hfit)

theorem hypermapFourColor_of_redpartAllPresentations_plainCubicMirror
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshortNode : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u})
    (hfit : Presentation.PlainCubicFitpMirror.{u}) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample_reduction
    (noMinimalCounterexample_of_redpartAllPresentations_plainCubicMirror
      hconnected hshortNode heven hshortFace
      hredCert hredpart hfit)

theorem noMinimalCounterexample_of_redpartAllPresentations_plainCubicMirror_proved
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshortNode : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u}) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_redpartAllPresentations_plainCubicMirror
    hconnected hshortNode heven hshortFace
    hredCert hredpart
    Presentation.plainCubicFitpMirror

theorem hypermapFourColor_of_redpartAllPresentations_plainCubicMirror_proved
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshortNode : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u}) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample_reduction
    (noMinimalCounterexample_of_redpartAllPresentations_plainCubicMirror_proved
      hconnected hshortNode heven hshortFace
      hredCert hredpart)

theorem noMinimalCounterexample_of_redpartAllPresentations_plainCubicMirrorUpToEleven
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshortNode : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u})
    (hfit : Presentation.PlainCubicFitpMirrorUpTo.{u} 11) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_redpartAllPresentations_upToEleven
    hconnected hshortNode heven hshortFace
    hredCert hredpart
    (Unavoidability.mirrorValidHubTransport_of_noShortNodeOrbits hshortNode)
    (Presentation.mirrorExactFitTransportUpTo_of_plainCubic_fitp_mirror_upTo
      (Unavoidability.cubicMinimalCounterexamples_of_noShortNodeOrbits
        hshortNode)
      hfit)

theorem hypermapFourColor_of_redpartAllPresentations_plainCubicMirrorUpToEleven
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshortNode : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u})
    (hfit : Presentation.PlainCubicFitpMirrorUpTo.{u} 11) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample_reduction
    (noMinimalCounterexample_of_redpartAllPresentations_plainCubicMirrorUpToEleven
      hconnected hshortNode heven hshortFace hredCert hredpart hfit)

theorem noMinimalCounterexample_of_redpartAllPresentations_plainCubicMirrorUpToEleven_proved
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshortNode : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u}) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_redpartAllPresentations_plainCubicMirrorUpToEleven
    hconnected hshortNode heven hshortFace hredCert hredpart
    (Presentation.plainCubicFitpMirrorUpTo_of_plainCubicFitpMirror
      Presentation.plainCubicFitpMirror)

theorem hypermapFourColor_of_redpartAllPresentations_plainCubicMirrorUpToEleven_proved
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshortNode : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u}) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample_reduction
    (noMinimalCounterexample_of_redpartAllPresentations_plainCubicMirrorUpToEleven_proved
      hconnected hshortNode heven hshortFace hredCert hredpart)

theorem noMinimalCounterexample_of_redpartAllPresentations_plainCubicMirror_walkupCounts
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u}) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_redpartAllPresentations_plainCubicMirror_proved
    hconnected
    Unavoidability.noShortNodeOrbitsMinimalCounterexamples_proved
    heven hshortFace hredCert hredpart

theorem hypermapFourColor_of_redpartAllPresentations_plainCubicMirror_walkupCounts
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u}) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample_reduction
    (noMinimalCounterexample_of_redpartAllPresentations_plainCubicMirror_walkupCounts
      hconnected heven hshortFace hredCert hredpart)

theorem noMinimalCounterexample_of_redpartAllPresentations_plainCubicMirrorUpToEleven_walkupCounts
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u}) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_redpartAllPresentations_plainCubicMirrorUpToEleven_proved
    hconnected
    Unavoidability.noShortNodeOrbitsMinimalCounterexamples_proved
    heven hshortFace hredCert hredpart

theorem hypermapFourColor_of_redpartAllPresentations_plainCubicMirrorUpToEleven_walkupCounts
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u}) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample_reduction
    (noMinimalCounterexample_of_redpartAllPresentations_plainCubicMirrorUpToEleven_walkupCounts
      hconnected heven hshortFace hredCert hredpart)

theorem noMinimalCounterexample_of_redpartAllPresentations_provedStructural
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u})
    (hvalid : Presentation.MirrorValidHubTransport.{u})
    (hfitMirror : Presentation.MirrorExactFitTransport.{u}) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_redpartAllPresentations
    Unavoidability.connectedMinimalCounterexamples_proved
    Unavoidability.noShortNodeOrbitsMinimalCounterexamples_proved
    Unavoidability.evenGenusMinimalCounterexamples_proved
    hshortFace hredCert hredpart hvalid hfitMirror

theorem hypermapFourColor_of_redpartAllPresentations_provedStructural
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u})
    (hvalid : Presentation.MirrorValidHubTransport.{u})
    (hfitMirror : Presentation.MirrorExactFitTransport.{u}) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample_reduction
    (noMinimalCounterexample_of_redpartAllPresentations_provedStructural
      hshortFace hredCert hredpart hvalid hfitMirror)

theorem noMinimalCounterexample_of_faceArityRedpartAllPresentations_provedStructural
    (harity : Unavoidability.FaceArityGeFiveMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u})
    (hvalid : Presentation.MirrorValidHubTransport.{u})
    (hfitMirror : Presentation.MirrorExactFitTransport.{u}) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_redpartAllPresentations_provedStructural
    (Unavoidability.noShortFaceOrbitsMinimalCounterexamples_of_faceArityGeFive
      harity)
    hredCert hredpart hvalid hfitMirror

theorem hypermapFourColor_of_faceArityRedpartAllPresentations_provedStructural
    (harity : Unavoidability.FaceArityGeFiveMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u})
    (hvalid : Presentation.MirrorValidHubTransport.{u})
    (hfitMirror : Presentation.MirrorExactFitTransport.{u}) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample_reduction
    (noMinimalCounterexample_of_faceArityRedpartAllPresentations_provedStructural
      harity hredCert hredpart hvalid hfitMirror)

theorem noMinimalCounterexample_of_redpartAllPresentations_plainCubicMirror_provedStructural
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u}) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_redpartAllPresentations_plainCubicMirror_proved
    Unavoidability.connectedMinimalCounterexamples_proved
    Unavoidability.noShortNodeOrbitsMinimalCounterexamples_proved
    Unavoidability.evenGenusMinimalCounterexamples_proved
    hshortFace hredCert hredpart

theorem hypermapFourColor_of_redpartAllPresentations_plainCubicMirror_provedStructural
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u}) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample_reduction
    (noMinimalCounterexample_of_redpartAllPresentations_plainCubicMirror_provedStructural
      hshortFace hredCert hredpart)

theorem noMinimalCounterexample_of_faceArityRedpartAllPresentations_plainCubicMirror_provedStructural
    (harity : Unavoidability.FaceArityGeFiveMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u}) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_redpartAllPresentations_plainCubicMirror_provedStructural
    (Unavoidability.noShortFaceOrbitsMinimalCounterexamples_of_faceArityGeFive
      harity)
    hredCert hredpart

theorem hypermapFourColor_of_faceArityRedpartAllPresentations_plainCubicMirror_provedStructural
    (harity : Unavoidability.FaceArityGeFiveMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u}) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample_reduction
    (noMinimalCounterexample_of_faceArityRedpartAllPresentations_plainCubicMirror_provedStructural
      harity hredCert hredpart)

theorem noMinimalCounterexample_of_redpartAllPresentations_plainCubicMirrorUpToEleven_provedStructural
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u}) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_redpartAllPresentations_plainCubicMirrorUpToEleven_proved
    Unavoidability.connectedMinimalCounterexamples_proved
    Unavoidability.noShortNodeOrbitsMinimalCounterexamples_proved
    Unavoidability.evenGenusMinimalCounterexamples_proved
    hshortFace hredCert hredpart

theorem hypermapFourColor_of_redpartAllPresentations_plainCubicMirrorUpToEleven_provedStructural
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u}) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample_reduction
    (noMinimalCounterexample_of_redpartAllPresentations_plainCubicMirrorUpToEleven_provedStructural
      hshortFace hredCert hredpart)

theorem noMinimalCounterexample_of_faceArityRedpartAllPresentations_plainCubicMirrorUpToEleven_provedStructural
    (harity : Unavoidability.FaceArityGeFiveMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u}) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_redpartAllPresentations_plainCubicMirrorUpToEleven_provedStructural
    (Unavoidability.noShortFaceOrbitsMinimalCounterexamples_of_faceArityGeFive
      harity)
    hredCert hredpart

theorem hypermapFourColor_of_faceArityRedpartAllPresentations_plainCubicMirrorUpToEleven_provedStructural
    (harity : Unavoidability.FaceArityGeFiveMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u}) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample_reduction
    (noMinimalCounterexample_of_faceArityRedpartAllPresentations_plainCubicMirrorUpToEleven_provedStructural
      harity hredCert hredpart)

theorem noMinimalCounterexample_of_noConfigQuizMirrorFit_plainCubicMirrorUpToEleven_provedStructural
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hnofit : Presentation.NoConfigQuizMirrorFitMinimalCounterexamples.{u}) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_redpartAllPresentations_plainCubicMirrorUpToEleven_provedStructural
    hshortFace hredCert
    (Presentation.redpartSound_of_noConfigQuizMirrorFit
      (Unavoidability.cubicMinimalCounterexamples_of_noShortNodeOrbits
        Unavoidability.noShortNodeOrbitsMinimalCounterexamples_proved)
      hnofit)

theorem hypermapFourColor_of_noConfigQuizMirrorFit_plainCubicMirrorUpToEleven_provedStructural
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hnofit : Presentation.NoConfigQuizMirrorFitMinimalCounterexamples.{u}) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample_reduction
    (noMinimalCounterexample_of_noConfigQuizMirrorFit_plainCubicMirrorUpToEleven_provedStructural
      hshortFace hredCert hnofit)

theorem noMinimalCounterexample_of_faceArityNoConfigQuizMirrorFit_plainCubicMirrorUpToEleven_provedStructural
    (harity : Unavoidability.FaceArityGeFiveMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hnofit : Presentation.NoConfigQuizMirrorFitMinimalCounterexamples.{u}) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_noConfigQuizMirrorFit_plainCubicMirrorUpToEleven_provedStructural
    (Unavoidability.noShortFaceOrbitsMinimalCounterexamples_of_faceArityGeFive
      harity)
    hredCert hnofit

theorem hypermapFourColor_of_faceArityNoConfigQuizMirrorFit_plainCubicMirrorUpToEleven_provedStructural
    (harity : Unavoidability.FaceArityGeFiveMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hnofit : Presentation.NoConfigQuizMirrorFitMinimalCounterexamples.{u}) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample_reduction
    (noMinimalCounterexample_of_faceArityNoConfigQuizMirrorFit_plainCubicMirrorUpToEleven_provedStructural
      harity hredCert hnofit)

theorem noMinimalCounterexample_of_interfaces_plainCubicMirrorUpToEleven_provedStructural
    (hshortFace :
      Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{0})
    (hsource : Presentation.ConfigQuizSourceValidTheConfigs)
    (hno : Presentation.NoConfigPreembeddingMinimalCounterexamples)
    (hredCert : Presentation.Reducibility) :
    NoMinimalCounterexample.{0} :=
  noMinimalCounterexample_of_noConfigQuizMirrorFit_plainCubicMirrorUpToEleven_provedStructural
    hshortFace hredCert
    (Presentation.noConfigQuizMirrorFitMinimalCounterexamples_of_interfaces_zero
      (Unavoidability.cubicMinimalCounterexamples_of_noShortNodeOrbits
        Unavoidability.noShortNodeOrbitsMinimalCounterexamples_proved)
      hsource hno)

theorem hypermapFourColor_of_interfaces_plainCubicMirrorUpToEleven_provedStructural
    (hshortFace :
      Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{0})
    (hsource : Presentation.ConfigQuizSourceValidTheConfigs)
    (hno : Presentation.NoConfigPreembeddingMinimalCounterexamples)
    (hredCert : Presentation.Reducibility) :
    HypermapFourColorTheorem.{0} :=
  hypermapFourColor_of_no_minimalCounterexample_reduction
    (noMinimalCounterexample_of_interfaces_plainCubicMirrorUpToEleven_provedStructural
      hshortFace hsource hno hredCert)

theorem noMinimalCounterexample_of_faceArityInterfaces_plainCubicMirrorUpToEleven_provedStructural
    (harity : Unavoidability.FaceArityGeFiveMinimalCounterexamples.{0})
    (hsource : Presentation.ConfigQuizSourceValidTheConfigs)
    (hno : Presentation.NoConfigPreembeddingMinimalCounterexamples)
    (hredCert : Presentation.Reducibility) :
    NoMinimalCounterexample.{0} :=
  noMinimalCounterexample_of_interfaces_plainCubicMirrorUpToEleven_provedStructural
    (Unavoidability.noShortFaceOrbitsMinimalCounterexamples_of_faceArityGeFive
      harity)
    hsource hno hredCert

theorem hypermapFourColor_of_faceArityInterfaces_plainCubicMirrorUpToEleven_provedStructural
    (harity : Unavoidability.FaceArityGeFiveMinimalCounterexamples.{0})
    (hsource : Presentation.ConfigQuizSourceValidTheConfigs)
    (hno : Presentation.NoConfigPreembeddingMinimalCounterexamples)
    (hredCert : Presentation.Reducibility) :
    HypermapFourColorTheorem.{0} :=
  hypermapFourColor_of_no_minimalCounterexample_reduction
    (noMinimalCounterexample_of_faceArityInterfaces_plainCubicMirrorUpToEleven_provedStructural
      harity hsource hno hredCert)

end

end CombinatorialFourColor

end FourColor

end Schematic.Math.GraphTheory
