module

public import SerrePositivity.InfinityCategories.F2.Presentable.FiniteOverCodes
public import SerrePositivity.InfinityCategories.F2.Presentable.ContinuousLeftFibrationAnodyne
public import SerrePositivity.InfinityCategories.F2.Ind.SmallSubcomplexFamilyColimit
public import SerrePositivity.InfinityCategories.F2.Ind.FilteredPosetNerve

/-!
概要：任意の底上の対象と、その連続置換を有限底上模型の filtered 余極限として表示する。
方針：元の有限部分複体の包含余錐を底上へ持ち上げ、同じ全余錐へ連続置換を適用する。
規約：このモジュールの余極限は通常の底上の圏の余極限。native な普遍性は別に証明する。
使われ方：前層の小さい compact 生成族への全表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

local instance : Fact Cardinal.aleph0.IsRegular := ⟨Cardinal.isRegular_aleph0⟩

/-- 元の全空間の有限部分複体の小さい包含順。 -/
abbrev FiniteOverPieces {B : SSet.{u}} (X : Over B) :=
  Ind.SmallSubcomplexFamily Cardinal.aleph0 X.left (fun _ ↦ True)

instance finiteOverPieces_isFiltered {B : SSet.{u}} (X : Over B) :
    IsFiltered (FiniteOverPieces X) :=
  isFiltered_of_isCardinalFiltered _ Cardinal.aleph0

instance finiteOverPiece_finite {B : SSet.{u}} {X : Over B} (A : FiniteOverPieces X) :
    A.val.toSSet.Finite := ⟨Cardinal.lt_aleph0_iff_finite.mp A.property.1⟩

/-- 元の有限部分複体の nerve は、全 coherent な試験図式に対して filtered。 -/
lemma finiteOverPieces_nerve_isKappaFiltered {B : SSet.{u}} (X : Over B) :
    IsKappaFiltered Cardinal.aleph0 (nerve (FiniteOverPieces X)) :=
  Ind.isKappaFiltered_nerve_of_cardinalFiltered _

/-- 同じ有限部分複体に元の底への射を添えた全図式。 -/
def finiteOverPiecesDiagram {B : SSet.{u}} (X : Over B) : FiniteOverPieces X ⥤ Over B :=
  Over.lift (Ind.smallSubcomplexFamilyDiagram Cardinal.aleph0 X.left (fun _ ↦ True))
    ((Ind.smallSubcomplexFamilyCocone Cardinal.aleph0 X.left (fun _ ↦ True)).ι ≫
      (Functor.const (FiniteOverPieces X)).map X.hom)

/-- 元の底上の対象への、同じ全包含を脚とする余錐。 -/
def finiteOverPiecesCocone {B : SSet.{u}} (X : Over B) : Cocone (finiteOverPiecesDiagram X) where
  pt := X
  ι := {
    app A := Over.homMk A.val.ι rfl
    naturality _ _ f := Over.OverMorphism.ext
      ((Ind.smallSubcomplexFamilyCocone Cardinal.aleph0 X.left (fun _ ↦ True)).w f) }

/-- 同じ底上の全包含余錐は通常の filtered 余極限である。 -/
def finiteOverPiecesCocone_isColimit {B : SSet.{u}} (X : Over B) :
    IsColimit (finiteOverPiecesCocone X) := by
  apply isColimitOfReflects (Over.forget B)
  exact Ind.smallSubcomplexFamilyCocone_isColimit Cardinal.aleph0 X.left (fun _ ↦ True)
    (fun A hA ↦ ⟨A, hA, trivial, le_rfl⟩)

/-- 同じ有限底上模型の連続 left fibration 置換の図式。 -/
def finiteOverReplacementDiagram {B : SSet.{u}} (X : Over B) : FiniteOverPieces X ⥤ Over B :=
  finiteOverPiecesDiagram X ⋙ continuousLeftFibrationReplacement B

/-- 元の同じ全包含余錐の連続置換。 -/
def finiteOverReplacementCocone {B : SSet.{u}} (X : Over B) :
    Cocone (finiteOverReplacementDiagram X) :=
  (continuousLeftFibrationReplacement B).mapCocone (finiteOverPiecesCocone X)

/-- 同じ置換後の全余錐は、通常の底上の圏で filtered 余極限。 -/
def finiteOverReplacementCocone_isColimit {B : SSet.{u}} (X : Over B) :
    IsColimit (finiteOverReplacementCocone X) :=
  isColimitOfPreserves (continuousLeftFibrationReplacement B) (finiteOverPiecesCocone_isColimit X)

/-- 各置換後の項は、同じ小さい有限符号族の置換の一つと底上で同型である。 -/
lemma finiteOverReplacementDiagram_in_family {B : SSet.{u}} (X : Over B)
    (A : FiniteOverPieces X) :
    ∃ q : FiniteOverCode B, Nonempty
      ((continuousLeftFibrationReplacement B).obj q.realization ≅
        (finiteOverReplacementDiagram X).obj A) := by
  have : ((finiteOverPiecesDiagram X).obj A).left.Finite := inferInstanceAs A.val.toSSet.Finite
  obtain ⟨q, ⟨e⟩⟩ := exists_finiteOverCode ((finiteOverPiecesDiagram X).obj A)
  exact ⟨q, ⟨(continuousLeftFibrationReplacement B).mapIso e⟩⟩

end SerrePositivity.InfinityCategories.F2.Presentable
