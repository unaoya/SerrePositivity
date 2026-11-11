module

public import SerrePositivity.KST.LocalizingInvariants.SpectrumPreComposition

/-!
概要：BF の標準三角形の全辺比較を、指定始点を持つ射として計算する。
方針：元のホモトピーを端点だけ輸送し、三射の二つの全合成式を適用する。
規約：同じ全 h Fun 類を保持。使われ方：置換単位の相殺と模型右辺の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
open OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.SpectrumArrow

local instance arrowCalculusCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable {A B C D : OmegaSpectrum.{u}}

def diagram {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) :=
  SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge

def obj {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) :=
  HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (diagram f))

def post (a : A ⟶ B) (b : B ⟶ C) : obj a ⟶ obj (a ≫ b) :=
  Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (SpectrumTriangleNormalization.canonicalPost a b))

def pre (a : A ⟶ B) (b : B ⟶ C) : obj (a ≫ b) ⟶ obj b :=
  Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (SpectrumTriangleNormalization.canonicalPre a b))

def preAt (a : A ⟶ B) (b : B ⟶ C) {d : A ⟶ C} (h : a ≫ b = d) : obj d ⟶ obj b :=
  Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
    (HomotopyArrow.rebase (SpectrumTriangleNormalization.canonicalPre a b)
      (congrArg diagram h) rfl))

lemma preAt_arrow (a : A ⟶ B) (b : B ⟶ C) {d : A ⟶ C} (h : a ≫ b = d) :
    Arrow.mk (preAt a b h) = Arrow.mk (pre a b) :=
  (HomotopyArrow.rebase_arrow _ _ _).symm

lemma pre_comp_arrow (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D)
    {d : B ⟶ D} (h : b ≫ c = d) :
    Arrow.mk (pre a d ≫ preAt b c h) = Arrow.mk (pre (a ≫ b) c) := by
  subst d
  exact SpectrumTriangleNormalization.canonicalPre_comp_arrow a b c

lemma preAt_comp_arrow (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D)
    {d : B ⟶ D} {e : A ⟶ D} (h : b ≫ c = d) (k : a ≫ d = e) :
    Arrow.mk (preAt a d k ≫ preAt b c h) = Arrow.mk (pre (a ≫ b) c) :=
  (arrow_mk_comp_congr (preAt_arrow a d k) rfl).trans (pre_comp_arrow a b c h)

lemma overlap (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D)
    {d : A ⟶ C} (h : a ≫ b = d) :
    preAt a b h ≫ post b c = post d c ≫
      preAt a (b ≫ c) ((Category.assoc a b c).symm.trans (congrArg (· ≫ c) h)) := by
  subst d
  exact SpectrumTriangleNormalization.canonical_overlap a b c

end SerrePositivity.KST.LocalizingInvariants.SpectrumArrow
