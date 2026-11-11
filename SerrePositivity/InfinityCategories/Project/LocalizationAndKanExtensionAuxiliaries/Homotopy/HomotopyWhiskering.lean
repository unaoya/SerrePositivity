module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyRepresentative

/-!
概要：実際のホモトピーの前後合成と恒等を h Fun の作用に移す。
方針：raw な円柱の射を保持し、curry した代表辺を比較する。
規約：ホモトピー類から代表を選び直さない。
使われ方：B1 の comma 比較から三角恒等式を読む。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy

/-- 概要：ホモトピーを始域の射で前合成する。
方針：円柱のパラメータに前合成する。
規約：raw な射を保持する。使われ方：単位の G に沿う制限。 -/
def functorHomotopyPrecomp {A B X : SSet.{u}} {f g : B ⟶ X}
    (H : SSet.Homotopy f g) (i : A ⟶ B) : SSet.Homotopy (i ≫ f) (i ≫ g) where
  h := (i ▷ (Δ[1] : SSet.{u})) ≫ H.h
  h₀ := by rw [SSet.ι₀_comp_assoc, H.h₀]; rfl
  h₁ := by rw [SSet.ι₁_comp_assoc, H.h₁]; rfl
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

/-- 概要：ホモトピーを標的の射で後合成する。
方針：円柱の射を後合成する。
規約：raw な射を保持する。使われ方：余単位の G による像。 -/
def functorHomotopyPostcomp {A X Y : SSet.{u}} {f g : A ⟶ X}
    (H : SSet.Homotopy f g) (q : X ⟶ Y) : SSet.Homotopy (f ≫ q) (g ≫ q) where
  h := H.h ≫ q
  h₀ := by rw [← Category.assoc, H.h₀]; rfl
  h₁ := by rw [← Category.assoc, H.h₁]; rfl
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

/-- 概要：時間に定値なホモトピー。
方針：第一射影の後に指定した射を続ける。
規約：任意の単体集合。使われ方：三角恒等式の恒等辺の代表。 -/
def functorHomotopyRefl {A X : SSet.{u}} (f : A ⟶ X) : SSet.Homotopy f f where
  h := fst A (Δ[1] : SSet.{u}) ≫ f
  h₀ := by simp
  h₁ := by simp
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

/-- 概要：ホモトピーの前合成の類は h Fun の前合成の作用。
方針：curry と前合成の自然性で代表辺を比較する。
規約：任意のパラメータ。使われ方：単位の whisker の認識。 -/
lemma functorHomotopyPrecomp_hom {A B X : SSet.{u}} {f g : B ⟶ X}
    (H : SSet.Homotopy f g) (i : A ⟶ B) :
    SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (functorHomotopyPrecomp H i)) =
      (hoFunctor.map ((pre i).app X)).toFunctor.map
        (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) := by
  change SSet.Truncated.HomotopyCategory.homMk _ =
    SSet.Truncated.HomotopyCategory.homMk _
  congr 1

/-- 概要：ホモトピーの後合成の類は h Fun の後合成の作用。
方針：curry の後合成自然性で代表辺を比較する。
規約：任意のパラメータ。使われ方：余単位の whisker の認識。 -/
lemma functorHomotopyPostcomp_hom {A X Y : SSet.{u}} {f g : A ⟶ X}
    (H : SSet.Homotopy f g) (q : X ⟶ Y) :
    SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (functorHomotopyPostcomp H q)) =
      (hoFunctor.map ((ihom A).map q)).toFunctor.map
        (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) := by
  change SSet.Truncated.HomotopyCategory.homMk _ =
    SSet.Truncated.HomotopyCategory.homMk _
  congr 1

/-- 概要：時間に定値なホモトピーの類は恒等射。
方針：curry した円柱を定値関手の辺へ認識する。
規約：quasicategory 性は不要。使われ方：三角恒等式の右辺の単純化。 -/
lemma functorHomotopyRefl_hom {A X : SSet.{u}} (f : A ⟶ X) :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (functorHomotopyRefl f)) = 𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) := by
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (functorHomotopyRefl f) =
      SSet.Truncated.Edge.id (X := (truncation 2).obj ((ihom A).obj X))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) := by
    apply SSet.Truncated.Edge.ext
    change SSet.yonedaEquiv (curry (fst A (Δ[1] : SSet.{u}) ≫ f)) = _
    have hc : curry (fst A (Δ[1] : SSet.{u}) ≫ f) =
        (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) : (Δ[1] : SSet.{u}) ⟶ (ihom A).obj X) := by
      apply uncurry_injective
      rw [uncurry_curry, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]
    rw [hc]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)
  rw [he, SSet.Truncated.HomotopyCategory.homMk_id]
  rfl

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
