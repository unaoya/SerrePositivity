module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNativeChosenFrameKan
public import SerrePositivity.InfinityCategories.F1.Universe.QCatEquivalence
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.WeakHomotopyPrecomposition

/-!
概要：元の二つの実混合比較を、大宇宙の同じ Kan 共通標的への自然変換にする。
方針：共通混合 Hom の実 Kan 置換単位を後合成し、同じ射を持ち上げる。
規約：追加の同値仮定・モデル構造入力なし。比較は全標的射に自然。
使われ方：選んだ right resolution と実始域 frame 図式の全自然同型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.Reedy
open SerrePositivity.InfinityCategories SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.InfinityCategories.F2
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (A : Mon (Complex R))

def nativeCellChosenMixedLeftToKan : cosimplicialHom (nativeCellSourceFrame R A) ⟶
    nativeCellChosenMixedMappingFunctor R A ⋙ continuousKanReplacement :=
  nativeCellChosenMixedLeft R A ≫
    Functor.whiskerLeft (nativeCellChosenMixedMappingFunctor R A) continuousKanReplacementUnit

def nativeCellChosenMixedRightToKan : nativeCellChosenRightMappingFunctor R A ⟶
    nativeCellChosenMixedMappingFunctor R A ⋙ continuousKanReplacement :=
  nativeCellChosenMixedRight R A ≫
    Functor.whiskerLeft (nativeCellChosenMixedMappingFunctor R A) continuousKanReplacementUnit

lemma nativeCellChosenMixedLeftToKan_weakEquivalence (B : Mon (Complex R)) :
    IsWeakHomotopyEquivalence ((nativeCellChosenMixedLeftToKan R A).app B) :=
  (nativeCellChosenMixedLeft_weakEquivalence R A B).comp
    (continuousKanReplacementUnit_isWeakHomotopyEquivalence _)

lemma nativeCellChosenMixedRightToKan_weakEquivalence (B : Mon (Complex R)) :
    IsWeakHomotopyEquivalence ((nativeCellChosenMixedRightToKan R A).app B) :=
  (nativeCellChosenMixedRight_weakEquivalence R A B).comp
    (continuousKanReplacementUnit_isWeakHomotopyEquivalence _)

def nativeCellChosenMixedLeftLarge :
    nativeCellSourceFrameLargeKanFunctor R A ⋙ kanObjectForget ⟶
      nativeCellChosenMixedReplacementLargeKanFunctor R A ⋙ kanObjectForget :=
  Functor.whiskerRight (nativeCellChosenMixedLeftToKan R A) SSet.uliftFunctor.{u + 1, u}

def nativeCellChosenMixedRightLarge :
    nativeCellChosenRightLargeKanFunctor R A ⋙ kanObjectForget ⟶
      nativeCellChosenMixedReplacementLargeKanFunctor R A ⋙ kanObjectForget :=
  Functor.whiskerRight (nativeCellChosenMixedRightToKan R A) SSet.uliftFunctor.{u + 1, u}

lemma nativeCellChosenMixedLeftLarge_isQCatEquivalence (B : Mon (Complex R)) :
    IsQCatEquivalence
      (show ((nativeCellSourceFrameLargeKanFunctor R A).obj B).obj ⟶
        ((nativeCellChosenMixedReplacementLargeKanFunctor R A).obj B).obj from
          (nativeCellChosenMixedLeftLarge R A).app B) := by
  have := nativeCellSourceFrameHom_kanComplex R A B
  have : SSet.KanComplex ((nativeCellChosenMixedMappingFunctor R A ⋙
      continuousKanReplacement).obj B) := continuousKanReplacement_kanComplex _
  exact IsQCatEquivalence.ulift.{u, u + 1}
    (IsSimplicialHomotopyEquivalence.isQCatEquivalence
      (nativeCellChosenMixedLeftToKan_weakEquivalence R A B).isSimplicialHomotopyEquivalence)

lemma nativeCellChosenMixedRightLarge_isQCatEquivalence (B : Mon (Complex R)) :
    IsQCatEquivalence
      (show ((nativeCellChosenRightLargeKanFunctor R A).obj B).obj ⟶
        ((nativeCellChosenMixedReplacementLargeKanFunctor R A).obj B).obj from
          (nativeCellChosenMixedRightLarge R A).app B) := by
  have : SSet.KanComplex ((nativeCellChosenRightMappingFunctor R A).obj B) :=
    nativeCellChosenRightMapping_kanComplex R A B
  have : SSet.KanComplex ((nativeCellChosenMixedMappingFunctor R A ⋙
      continuousKanReplacement).obj B) := continuousKanReplacement_kanComplex _
  exact IsQCatEquivalence.ulift.{u, u + 1}
    (IsSimplicialHomotopyEquivalence.isQCatEquivalence
      (nativeCellChosenMixedRightToKan_weakEquivalence R A B).isSimplicialHomotopyEquivalence)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
