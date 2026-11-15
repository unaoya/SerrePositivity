module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.CosliceTwistedHomEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseLeftFilling
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceModelEquivalence
/-!
概要：同じtwisted Homとその反転を、既存のcosliceとedgewiseの比較でpinched Homへ運ぶ。
方針：既存比較の指定された逆を合成し、同じ単位三角形を全関手同型で保持する。
規約：任意の準圏に対する既存比較の合成。単体集合のモデル構造を仮定しない。
使われ方：元のnative fiber射と基準roof射を同じ標的で照合する。
-/
@[expose] public noncomputable section
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open scoped Simplicial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
variable {C : SSet.{u}} [Quasicategory C] (x y : C _⦋0⦌)
/-- 既存のcoslice比較の逆と同じ右写像空間比較を合成する。 -/
def twistedArrowHomPinchedEquivalence :
    QCatEquivalence (twistedArrowHomSpace x y) (Basic.pinchedHom x y) :=
  (cosliceTwistedHomMap_isQCatEquivalence x y).choose.symm.trans
    (cosliceFiberRightMappingEquivalence x y)
/-- Kanな同じtwisted Homの反転を、既存edgewiseの二射影で戻す。 -/
def twistedArrowHomOppositePinchedEquivalence :
    QCatEquivalence (twistedArrowHomSpace x y).op (Basic.pinchedHom x y) :=
  ((isQCatEquivalence_of_trivialKanFibration
    (edgewiseLeft (twistedArrowHomSpace x y))).choose.symm.trans
      (isQCatEquivalence_of_trivialKanFibration
        (edgewiseRight (twistedArrowHomSpace x y))).choose).trans
          (twistedArrowHomPinchedEquivalence x y)
/-- 順射は同じ二射影と同じcoslice比較の指定逆の合成そのもの。 -/
theorem twistedArrowHomOppositePinchedEquivalence_hom :
    (twistedArrowHomOppositePinchedEquivalence x y).hom =
      (isQCatEquivalence_of_trivialKanFibration
        (edgewiseLeft (twistedArrowHomSpace x y))).choose.inv ≫
      edgewiseRight (twistedArrowHomSpace x y) ≫
      (cosliceTwistedHomMap_isQCatEquivalence x y).choose.inv ≫
      (cosliceFiberRightMappingEquivalence x y).hom := rfl
/-- 同じcoslice比較との三角形を全関手同型として保持する。 -/
def twistedArrowHomPinchedEquivalence_coslice :
    FunctorIso (cosliceTwistedHomMap x y ≫ (twistedArrowHomPinchedEquivalence x y).hom)
      (cosliceFiberRightMappingEquivalence x y).hom := by
  change FunctorIso
    (cosliceTwistedHomMap x y ≫ (cosliceTwistedHomMap_isQCatEquivalence x y).choose.inv ≫
      (cosliceFiberRightMappingEquivalence x y).hom)
    (cosliceFiberRightMappingEquivalence x y).hom
  simpa only [IsQCatEquivalence.choose, Category.assoc, Category.id_comp] using
    ((cosliceTwistedHomMap_isQCatEquivalence x y).choose.homInvIso.postcomp
      (cosliceFiberRightMappingEquivalence x y).hom)
/-- 同じedgewiseの二射影による反転の三角形も全関手同型で保持する。 -/
def twistedArrowHomOppositePinchedEquivalence_edgewise :
    FunctorIso
      (edgewiseLeft (twistedArrowHomSpace x y) ≫
        (twistedArrowHomOppositePinchedEquivalence x y).hom)
      (edgewiseRight (twistedArrowHomSpace x y) ≫
        (twistedArrowHomPinchedEquivalence x y).hom) := by
  change FunctorIso
    (edgewiseLeft (twistedArrowHomSpace x y) ≫
      ((isQCatEquivalence_of_trivialKanFibration
        (edgewiseLeft (twistedArrowHomSpace x y))).choose.inv ≫
        edgewiseRight (twistedArrowHomSpace x y)) ≫
          (twistedArrowHomPinchedEquivalence x y).hom) _
  simpa only [IsQCatEquivalence.choose, Category.assoc, Category.id_comp] using
    ((isQCatEquivalence_of_trivialKanFibration
      (edgewiseLeft (twistedArrowHomSpace x y))).choose.homInvIso.postcomp
        (edgewiseRight (twistedArrowHomSpace x y) ≫
          (twistedArrowHomPinchedEquivalence x y).hom))
end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
