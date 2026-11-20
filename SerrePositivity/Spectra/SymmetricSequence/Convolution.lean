module

public import SerrePositivity.Spectra.SymmetricSequence.Basic
public import SerrePositivity.CategoryTheory.Limits
public import Mathlib.CategoryTheory.Monoidal.ExternalProduct.Basic
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

/-!
# 直和に沿う対称列の convolution

外部テンソル積を有限集合の直和に沿って左 Kan 拡張する。
小さい余極限から存在と普遍性を得て、二変数関手と各段の余極限表示を構成する。
添字圏のモノイダル構造と convolution の結合・単位の登録は、次の段階で行う。
-/

@[expose] public section

universe v u

noncomputable section

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasColimitsOfSize.{0, 0} C]

/-- 外部テンソル積の直和に沿う左 Kan 拡張は二変数で関手的。 -/
def convolutionFunctor : SymmetricSequence C × SymmetricSequence C ⥤ SymmetricSequence C :=
  externalProductBifunctor FiniteBijection FiniteBijection C ⋙ FiniteBijection.sumFunctor.lan

/-- 対称列の通常の convolution。 -/
abbrev convolution (F G : SymmetricSequence C) : SymmetricSequence C :=
  convolutionFunctor.obj (F, G)

/-- 各次数の積を convolution の和次数へ送る自然な射。 -/
def convolutionUnit (F G : SymmetricSequence C) :
    externalProduct F G ⟶ FiniteBijection.sumFunctor ⋙ convolution F G :=
  FiniteBijection.sumFunctor.leftKanExtensionUnit (externalProduct F G)

/-- この convolution は点ごとの左 Kan 拡張である。 -/
def convolutionIsPointwise (F G : SymmetricSequence C) :
    (Functor.LeftExtension.mk (convolution F G)
      (convolutionUnit F G)).IsPointwiseLeftKanExtension :=
  Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit _ _

instance convolution_isLeftKanExtension (F G : SymmetricSequence C) :
    (convolution F G).IsLeftKanExtension (convolutionUnit F G) :=
  (convolutionIsPointwise F G).isLeftKanExtension

/-- convolution の普遍性。直和の上に定義した積の射を一意に降ろせる。 -/
def convolutionHomEquiv (F G H : SymmetricSequence C) :
    (convolution F G ⟶ H) ≃ (externalProduct F G ⟶ FiniteBijection.sumFunctor ⋙ H) :=
  Functor.homEquivOfIsLeftKanExtension _ (convolutionUnit F G) H

/-- 第 n 段を作る分解の図式。対象は二つの有限集合と、その直和から n への全単射。 -/
def decompositionDiagram (F G : SymmetricSequence C) (n : ℕ) :
    CostructuredArrow FiniteBijection.sumFunctor (FiniteBijection.of n) ⥤ C :=
  CostructuredArrow.proj _ _ ⋙ externalProduct F G

/-- 各段は、直和からその段への全単射を添字とする余極限。 -/
def convolutionLevelIsoColimit (F G : SymmetricSequence C) (n : ℕ) :
    level (convolution F G) n ≅ colimit (decompositionDiagram F G n) :=
  FiniteBijection.sumFunctor.leftKanExtensionObjIsoColimit _ _

/-- 第 n 段の分解図式には、和次数が n の成分だけが現れる。 -/
lemma decomposition_card (n : ℕ)
    (d : CostructuredArrow FiniteBijection.sumFunctor (FiniteBijection.of n)) :
    FiniteBijection.card d.left.1 + FiniteBijection.card d.left.2 = n :=
  FiniteBijection.card_eq_of_hom d.hom

end SerrePositivity.SymmetricSequence
