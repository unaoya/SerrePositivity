module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNativeFrameKan
public import SerrePositivity.InfinityCategories.F1.Universe.QCatEquivalence
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.WeakHomotopyPrecomposition

/-!
概要：元の二つの実混合比較を、大宇宙の同じ Kan 共通標的への自然変換にする。
方針：共通混合 Hom の実 Kan 置換単位を後合成し、同じ射を持ち上げる。
規約：追加の同値仮定・モデル構造入力なし。比較は全標的射に自然。
使われ方：元の AW 空間値図式と実始域 frame 図式の全自然同型。
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

def nativeCellMixedLeftToKan : cosimplicialHom (nativeCellSourceFrame R A) ⟶
    nativeCellMixedMappingFunctor R A ⋙ continuousKanReplacement :=
  nativeCellMixedLeft R A ≫
    Functor.whiskerLeft (nativeCellMixedMappingFunctor R A) continuousKanReplacementUnit

def nativeCellMixedRightToKan : multiplicativeMappingFunctor R (cellResolution R A) ⟶
    nativeCellMixedMappingFunctor R A ⋙ continuousKanReplacement :=
  nativeCellMixedRight R A ≫
    Functor.whiskerLeft (nativeCellMixedMappingFunctor R A) continuousKanReplacementUnit

lemma nativeCellMixedLeftToKan_weakEquivalence (B : Mon (Complex R)) :
    IsWeakHomotopyEquivalence ((nativeCellMixedLeftToKan R A).app B) :=
  (nativeCellMixedLeft_weakEquivalence R A B).comp
    (continuousKanReplacementUnit_isWeakHomotopyEquivalence _)

lemma nativeCellMixedRightToKan_weakEquivalence (B : Mon (Complex R)) :
    IsWeakHomotopyEquivalence ((nativeCellMixedRightToKan R A).app B) :=
  (nativeCellMixedRight_weakEquivalence R A B).comp
    (continuousKanReplacementUnit_isWeakHomotopyEquivalence _)

def nativeCellMixedLeftLarge :
    nativeCellSourceFrameLargeKanFunctor R A ⋙ kanObjectForget ⟶
      nativeCellMixedReplacementLargeKanFunctor R A ⋙ kanObjectForget :=
  Functor.whiskerRight (nativeCellMixedLeftToKan R A) SSet.uliftFunctor.{u + 1, u}

def nativeCellMixedRightLarge :
    multiplicativeCellMappingLargeKanFunctor R A ⋙ kanObjectForget ⟶
      nativeCellMixedReplacementLargeKanFunctor R A ⋙ kanObjectForget :=
  Functor.whiskerRight (nativeCellMixedRightToKan R A) SSet.uliftFunctor.{u + 1, u}

lemma nativeCellMixedLeftLarge_isQCatEquivalence (B : Mon (Complex R)) :
    IsQCatEquivalence
      (show ((nativeCellSourceFrameLargeKanFunctor R A).obj B).obj ⟶
        ((nativeCellMixedReplacementLargeKanFunctor R A).obj B).obj from
          (nativeCellMixedLeftLarge R A).app B) := by
  have := nativeCellSourceFrameHom_kanComplex R A B
  have : SSet.KanComplex ((nativeCellMixedMappingFunctor R A ⋙
      continuousKanReplacement).obj B) := continuousKanReplacement_kanComplex _
  exact IsQCatEquivalence.ulift.{u, u + 1}
    (IsSimplicialHomotopyEquivalence.isQCatEquivalence
      (nativeCellMixedLeftToKan_weakEquivalence R A B).isSimplicialHomotopyEquivalence)

lemma nativeCellMixedRightLarge_isQCatEquivalence (B : Mon (Complex R)) :
    IsQCatEquivalence
      (show ((multiplicativeCellMappingLargeKanFunctor R A).obj B).obj ⟶
        ((nativeCellMixedReplacementLargeKanFunctor R A).obj B).obj from
          (nativeCellMixedRightLarge R A).app B) := by
  have : SSet.KanComplex ((multiplicativeMappingFunctor R (cellResolution R A)).obj B) :=
    multiplicativeCellMapping_kanComplex R A B
  have : SSet.KanComplex ((nativeCellMixedMappingFunctor R A ⋙
      continuousKanReplacement).obj B) := continuousKanReplacement_kanComplex _
  exact IsQCatEquivalence.ulift.{u, u + 1}
    (IsSimplicialHomotopyEquivalence.isQCatEquivalence
      (nativeCellMixedRightToKan_weakEquivalence R A B).isSimplicialHomotopyEquivalence)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
