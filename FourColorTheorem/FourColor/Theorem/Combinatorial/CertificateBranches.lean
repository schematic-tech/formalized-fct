import FourColorTheorem.FourColor.Theorem.Combinatorial.CanonicalReduction

/-! Local checker and reducibility-certificate endpoints. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace CombinatorialFourColor

universe u

noncomputable section

theorem noMinimalCounterexample_of_localBranchesAndPresentations
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshortNode : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hcap : Unavoidability.Dscore1LeFiveMinimalCounterexamples.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11))
    (hredCert : Presentation.Reducibility) :
    NoMinimalCounterexample.{u} :=
  Unavoidability.no_minimalCounterexample_of_localBranchesAndPresentations
    hconnected hshortNode heven hshortFace hcap
    h5 h6 h7 h8 h9 h10 h11 hredCert

theorem hypermapFourColor_of_localBranchesAndPresentations
    (hredMin : MinimalCounterexampleReduction.{u})
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshortNode : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hcap : Unavoidability.Dscore1LeFiveMinimalCounterexamples.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11))
    (hredCert : Presentation.Reducibility) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample hredMin
    (noMinimalCounterexample_of_localBranchesAndPresentations
      hconnected hshortNode heven hshortFace hcap
      h5 h6 h7 h8 h9 h10 h11 hredCert)

theorem hypermapFourColor_of_localBranchesAndPresentations_reduction
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshortNode : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hcap : Unavoidability.Dscore1LeFiveMinimalCounterexamples.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11))
    (hredCert : Presentation.Reducibility) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample_reduction
    (noMinimalCounterexample_of_localBranchesAndPresentations
      hconnected hshortNode heven hshortFace hcap
      h5 h6 h7 h8 h9 h10 h11 hredCert)

theorem noMinimalCounterexample_of_checkSoundAndPresentations
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshortNode : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u})
    (hsourceSound : Unavoidability.SmallSourceCheckSound.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11)) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_localBranchesAndPresentations
    hconnected hshortNode heven hshortFace
    (Unavoidability.dscore1LeFiveMinimalCounterexamples_of_checkSound
      hredpart hsourceSound)
    h5 h6 h7 h8 h9 h10 h11 hredCert

theorem hypermapFourColor_of_checkSoundAndPresentations
    (hredMin : MinimalCounterexampleReduction.{u})
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshortNode : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u})
    (hsourceSound : Unavoidability.SmallSourceCheckSound.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11)) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample hredMin
    (noMinimalCounterexample_of_checkSoundAndPresentations
      hconnected hshortNode heven hshortFace
      hredCert hredpart hsourceSound
      h5 h6 h7 h8 h9 h10 h11)

theorem hypermapFourColor_of_checkSoundAndPresentations_reduction
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshortNode : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u})
    (hsourceSound : Unavoidability.SmallSourceCheckSound.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11)) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample_reduction
    (noMinimalCounterexample_of_checkSoundAndPresentations
      hconnected hshortNode heven hshortFace
      hredCert hredpart hsourceSound
      h5 h6 h7 h8 h9 h10 h11)

theorem noMinimalCounterexample_of_redpartAndPresentations
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshortNode : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11)) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_localBranchesAndPresentations
    hconnected hshortNode heven hshortFace
    (Unavoidability.dscore1LeFiveMinimalCounterexamples_of_redpart
      hredpart)
    h5 h6 h7 h8 h9 h10 h11 hredCert

theorem noMinimalCounterexample_of_faceArityRedpartAndPresentations
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshortNode : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (harity : Unavoidability.FaceArityGeFiveMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11)) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_redpartAndPresentations
    hconnected hshortNode heven
    (Unavoidability.noShortFaceOrbitsMinimalCounterexamples_of_faceArityGeFive
      harity)
    hredCert hredpart
    h5 h6 h7 h8 h9 h10 h11

theorem noMinimalCounterexample_of_provedStructural_redpartAndPresentations
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11)) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_redpartAndPresentations
    Unavoidability.connectedMinimalCounterexamples_proved
    Unavoidability.noShortNodeOrbitsMinimalCounterexamples_proved
    Unavoidability.evenGenusMinimalCounterexamples_proved
    hshortFace hredCert hredpart
    h5 h6 h7 h8 h9 h10 h11

theorem noMinimalCounterexample_of_provedStructural_faceArityRedpartAndPresentations
    (harity : Unavoidability.FaceArityGeFiveMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11)) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_faceArityRedpartAndPresentations
    Unavoidability.connectedMinimalCounterexamples_proved
    Unavoidability.noShortNodeOrbitsMinimalCounterexamples_proved
    Unavoidability.evenGenusMinimalCounterexamples_proved
    harity hredCert hredpart
    h5 h6 h7 h8 h9 h10 h11

theorem redpartSound_of_noQuizTreeFit_provedCubic
    (hnofit : Presentation.NoQuizTreeFitMinimalCounterexamples.{u}) :
    Presentation.RedpartSound.{u} :=
  Presentation.redpartSound_of_noQuizTreeFit
    Unavoidability.cubicMinimalCounterexamples_proved
    hnofit

theorem redpartSound_of_noConfigQuizMirrorFit_provedCubic
    (hnofit : Presentation.NoConfigQuizMirrorFitMinimalCounterexamples.{u}) :
    Presentation.RedpartSound.{u} :=
  Presentation.redpartSound_of_noConfigQuizMirrorFit
    Unavoidability.cubicMinimalCounterexamples_proved
    hnofit

theorem noMinimalCounterexample_of_provedStructural_noQuizTreeFitAndPresentations
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hnofit : Presentation.NoQuizTreeFitMinimalCounterexamples.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11)) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_provedStructural_redpartAndPresentations
    hshortFace hredCert
    (redpartSound_of_noQuizTreeFit_provedCubic hnofit)
    h5 h6 h7 h8 h9 h10 h11

theorem noMinimalCounterexample_of_provedStructural_faceArityNoQuizTreeFitAndPresentations
    (harity : Unavoidability.FaceArityGeFiveMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hnofit : Presentation.NoQuizTreeFitMinimalCounterexamples.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11)) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_provedStructural_faceArityRedpartAndPresentations
    harity hredCert
    (redpartSound_of_noQuizTreeFit_provedCubic hnofit)
    h5 h6 h7 h8 h9 h10 h11

theorem noMinimalCounterexample_of_provedStructural_noConfigQuizMirrorFitAndPresentations
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hnofit : Presentation.NoConfigQuizMirrorFitMinimalCounterexamples.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11)) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_provedStructural_redpartAndPresentations
    hshortFace hredCert
    (redpartSound_of_noConfigQuizMirrorFit_provedCubic hnofit)
    h5 h6 h7 h8 h9 h10 h11

theorem noMinimalCounterexample_of_provedStructural_faceArityNoConfigQuizMirrorFitAndPresentations
    (harity : Unavoidability.FaceArityGeFiveMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hnofit : Presentation.NoConfigQuizMirrorFitMinimalCounterexamples.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11)) :
    NoMinimalCounterexample.{u} :=
  noMinimalCounterexample_of_provedStructural_faceArityRedpartAndPresentations
    harity hredCert
    (redpartSound_of_noConfigQuizMirrorFit_provedCubic hnofit)
    h5 h6 h7 h8 h9 h10 h11

theorem hypermapFourColor_of_redpartAndPresentations
    (hredMin : MinimalCounterexampleReduction.{u})
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshortNode : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11)) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample hredMin
    (noMinimalCounterexample_of_redpartAndPresentations
      hconnected hshortNode heven hshortFace
      hredCert hredpart
      h5 h6 h7 h8 h9 h10 h11)

theorem hypermapFourColor_of_provedStructural_redpartAndPresentations
    (hredMin : MinimalCounterexampleReduction.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11)) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample hredMin
    (noMinimalCounterexample_of_provedStructural_redpartAndPresentations
      hshortFace hredCert hredpart h5 h6 h7 h8 h9 h10 h11)

theorem hypermapFourColor_of_provedStructural_faceArityRedpartAndPresentations
    (hredMin : MinimalCounterexampleReduction.{u})
    (harity : Unavoidability.FaceArityGeFiveMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11)) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample hredMin
    (noMinimalCounterexample_of_provedStructural_faceArityRedpartAndPresentations
      harity hredCert hredpart h5 h6 h7 h8 h9 h10 h11)

theorem hypermapFourColor_of_provedStructural_noQuizTreeFitAndPresentations
    (hredMin : MinimalCounterexampleReduction.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hnofit : Presentation.NoQuizTreeFitMinimalCounterexamples.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11)) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample hredMin
    (noMinimalCounterexample_of_provedStructural_noQuizTreeFitAndPresentations
      hshortFace hredCert hnofit h5 h6 h7 h8 h9 h10 h11)

theorem hypermapFourColor_of_provedStructural_faceArityNoQuizTreeFitAndPresentations
    (hredMin : MinimalCounterexampleReduction.{u})
    (harity : Unavoidability.FaceArityGeFiveMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hnofit : Presentation.NoQuizTreeFitMinimalCounterexamples.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11)) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample hredMin
    (noMinimalCounterexample_of_provedStructural_faceArityNoQuizTreeFitAndPresentations
      harity hredCert hnofit h5 h6 h7 h8 h9 h10 h11)

theorem hypermapFourColor_of_provedStructural_noConfigQuizMirrorFitAndPresentations
    (hredMin : MinimalCounterexampleReduction.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hnofit : Presentation.NoConfigQuizMirrorFitMinimalCounterexamples.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11)) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample hredMin
    (noMinimalCounterexample_of_provedStructural_noConfigQuizMirrorFitAndPresentations
      hshortFace hredCert hnofit h5 h6 h7 h8 h9 h10 h11)

theorem hypermapFourColor_of_provedStructural_faceArityNoConfigQuizMirrorFitAndPresentations
    (hredMin : MinimalCounterexampleReduction.{u})
    (harity : Unavoidability.FaceArityGeFiveMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hnofit : Presentation.NoConfigQuizMirrorFitMinimalCounterexamples.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11)) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample hredMin
    (noMinimalCounterexample_of_provedStructural_faceArityNoConfigQuizMirrorFitAndPresentations
      harity hredCert hnofit h5 h6 h7 h8 h9 h10 h11)

theorem hypermapFourColor_of_redpartAndPresentations_reduction
    (hconnected : Unavoidability.ConnectedMinimalCounterexamples.{u})
    (hshortNode : Unavoidability.NoShortNodeOrbitsMinimalCounterexamples.{u})
    (heven : Unavoidability.EvenGenusMinimalCounterexamples.{u})
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11)) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample_reduction
    (noMinimalCounterexample_of_redpartAndPresentations
      hconnected hshortNode heven hshortFace
      hredCert hredpart
      h5 h6 h7 h8 h9 h10 h11)

theorem hypermapFourColor_of_provedStructural_redpartAndPresentations_reduction
    (hshortFace : Unavoidability.NoShortFaceOrbitsMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11)) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample_reduction
    (noMinimalCounterexample_of_provedStructural_redpartAndPresentations
      hshortFace hredCert hredpart h5 h6 h7 h8 h9 h10 h11)

theorem hypermapFourColor_of_provedStructural_faceArityRedpartAndPresentations_reduction
    (harity : Unavoidability.FaceArityGeFiveMinimalCounterexamples.{u})
    (hredCert : Presentation.Reducibility)
    (hredpart : Presentation.RedpartSound.{u})
    (h5 : Presentation.SucceedsIn.{u} (Part.pconsN 5) (Part.pconsN 5))
    (h6 : Presentation.SucceedsIn.{u} (Part.pconsN 6) (Part.pconsN 6))
    (h7 : Presentation.SucceedsIn.{u} (Part.pconsN 7) (Part.pconsN 7))
    (h8 : Presentation.SucceedsIn.{u} (Part.pconsN 8) (Part.pconsN 8))
    (h9 : Presentation.SucceedsIn.{u} (Part.pconsN 9) (Part.pconsN 9))
    (h10 : Presentation.SucceedsIn.{u} (Part.pconsN 10) (Part.pconsN 10))
    (h11 : Presentation.SucceedsIn.{u} (Part.pconsN 11) (Part.pconsN 11)) :
    HypermapFourColorTheorem.{u} :=
  hypermapFourColor_of_no_minimalCounterexample_reduction
    (noMinimalCounterexample_of_provedStructural_faceArityRedpartAndPresentations
      harity hredCert hredpart h5 h6 h7 h8 h9 h10 h11)


end

end CombinatorialFourColor

end FourColor

end Schematic.Math.GraphTheory
