module
public import SerrePositivity.KST.SConstruction.KanSpanPastingChoices
public import SerrePositivity.KST.SConstruction.RelativeAnodyneFamilyExtension
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-! # 二脚自体が変化する全ホーン族の貼り合わせ
概要：同じ始点族から出る二円柱を、一つの全パラメータの実ホーン族へ貼る。
方針：関手空間の元の二辺をホーンへ貼り、評価で元の実円柱を全次数で回収する。
規約：始点・二終点・二脚はすべてパラメータとともに変化してよい。
使われ方：高次入力から得た二円柱を、指定三角形境界を保つ実二単体族へ延長する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 元の全パラメータの二円柱を同じホーンへ貼り、実ホーン族として評価する。 -/
def varyingKanSpanHornFamily {U E : SSet.{u}} {D F G : U ⟶ E}
    (a : SSet.Homotopy D F) (b : SSet.Homotopy D G) :
    (Λ[2, 0] : SSet.{u}) ⊗ U ⟶ E :=
  (β_ (horn 2 (0 : Fin 3) : SSet.{u}) U).hom ≫ uncurry
    (kanSpanHorn (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy a))
      (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy b)))

/-- 変化するホーン族の第一脚は、元の全パラメータの第一円柱そのもの。 -/
lemma varyingKanSpanHornFamily_source {U E : SSet.{u}} {D F G : U ⟶ E}
    (a : SSet.Homotopy D F) (b : SSet.Homotopy D G) :
    (horn₂₀.ι₀₁ ▷ U) ≫ varyingKanSpanHornFamily a b =
      (β_ (Δ[1] : SSet.{u}) U).hom ≫ a.h := by
  rw [varyingKanSpanHornFamily, BraidedCategory.braiding_naturality_left_assoc,
    ← uncurry_natural_left, kanSpanHorn_source]
  change _ ≫ uncurry (curry a.h) = _
  rw [uncurry_curry]

/-- 変化するホーン族の第二脚も、元の全パラメータの第二円柱そのもの。 -/
lemma varyingKanSpanHornFamily_target {U E : SSet.{u}} {D F G : U ⟶ E}
    (a : SSet.Homotopy D F) (b : SSet.Homotopy D G) :
    (horn₂₀.ι₀₂ ▷ U) ≫ varyingKanSpanHornFamily a b =
      (β_ (Δ[1] : SSet.{u}) U).hom ≫ b.h := by
  rw [varyingKanSpanHornFamily, BraidedCategory.braiding_naturality_left_assoc,
    ← uncurry_natural_left, kanSpanHorn_target]
  change _ ≫ uncurry (curry b.h) = _
  rw [uncurry_curry]

/-- 二脚が変化する元のホーン族を、指定した境界三角形族を厳密に保持して延長する。 -/
def relativeVaryingKanSpanTriangleFamily {T U E : SSet.{u}} [KanComplex E]
    (j : T ⟶ U) [Mono j] {D F G : U ⟶ E}
    (a : SSet.Homotopy D F) (b : SSet.Homotopy D G)
    (R : (Δ[2] : SSet.{u}) ⊗ T ⟶ E)
    (h : ((horn 2 (0 : Fin 3)).ι ▷ T) ≫ R =
      ((horn 2 (0 : Fin 3) : SSet.{u}) ◁ j) ≫ varyingKanSpanHornFamily a b) :
    {L : (Δ[2] : SSet.{u}) ⊗ U ⟶ E //
      ((horn 2 (0 : Fin 3)).ι ▷ U) ≫ L = varyingKanSpanHornFamily a b ∧
      ((Δ[2] : SSet.{u}) ◁ j) ≫ L = R} :=
  relativeAnodyneFamilyExtension _ (anodyneExtensions.horn_ι (0 : Fin 3)) j _ R h

/-- 延長した全三角形族の第一面は、元の変化する第一円柱を厳密に回収する。 -/
lemma relativeVaryingKanSpanTriangleFamily_source {T U E : SSet.{u}} [KanComplex E]
    (j : T ⟶ U) [Mono j] {D F G : U ⟶ E}
    (a : SSet.Homotopy D F) (b : SSet.Homotopy D G)
    (R : (Δ[2] : SSet.{u}) ⊗ T ⟶ E)
    (h : ((horn 2 (0 : Fin 3)).ι ▷ T) ≫ R =
      ((horn 2 (0 : Fin 3) : SSet.{u}) ◁ j) ≫ varyingKanSpanHornFamily a b) :
    (stdSimplex.δ 2 ▷ U) ≫ (relativeVaryingKanSpanTriangleFamily j a b R h).val =
      (β_ (Δ[1] : SSet.{u}) U).hom ≫ a.h := by
  have he : (stdSimplex.δ 2 : (Δ[1] : SSet.{u}) ⟶ Δ[2]) =
      horn₂₀.ι₀₁ ≫ (horn 2 (0 : Fin 3)).ι := (horn.ι_ι _ _ (by decide)).symm
  rw [he, comp_whiskerRight_assoc,
    (relativeVaryingKanSpanTriangleFamily j a b R h).property.1, varyingKanSpanHornFamily_source]

/-- 延長した全三角形族の第二面も、元の変化する第二円柱を厳密に回収する。 -/
lemma relativeVaryingKanSpanTriangleFamily_target {T U E : SSet.{u}} [KanComplex E]
    (j : T ⟶ U) [Mono j] {D F G : U ⟶ E}
    (a : SSet.Homotopy D F) (b : SSet.Homotopy D G)
    (R : (Δ[2] : SSet.{u}) ⊗ T ⟶ E)
    (h : ((horn 2 (0 : Fin 3)).ι ▷ T) ≫ R =
      ((horn 2 (0 : Fin 3) : SSet.{u}) ◁ j) ≫ varyingKanSpanHornFamily a b) :
    (stdSimplex.δ 1 ▷ U) ≫ (relativeVaryingKanSpanTriangleFamily j a b R h).val =
      (β_ (Δ[1] : SSet.{u}) U).hom ≫ b.h := by
  have he : (stdSimplex.δ 1 : (Δ[1] : SSet.{u}) ⟶ Δ[2]) =
      horn₂₀.ι₀₂ ≫ (horn 2 (0 : Fin 3)).ι := (horn.ι_ι _ _ (by decide)).symm
  rw [he, comp_whiskerRight_assoc,
    (relativeVaryingKanSpanTriangleFamily j a b R h).property.1, varyingKanSpanHornFamily_target]

/-- 元のホーンへの貼り合わせは、写像空間の射による後合成と厳密に可換。 -/
lemma kanSpanHorn_postcomp {K L : SSet.{u}} {z x y : K _⦋0⦌}
    (a : K.Edge z x) (b : K.Edge z y) (q : K ⟶ L) :
    kanSpanHorn a b ≫ q = kanSpanHorn (a.map q) (b.map q) := by
  apply horn₂₀.isPushout.hom_ext
  · simp only [← Category.assoc, kanSpanHorn_source, SSet.yonedaEquiv_symm_comp]
    rfl
  · simp only [← Category.assoc, kanSpanHorn_target, SSet.yonedaEquiv_symm_comp]
    rfl

/-- 元の円柱を制限した関手辺は、同じ元の関手辺の写像空間での制限。 -/
lemma varyingKanSpanEdge_precomp {T U E : SSet.{u}} (j : T ⟶ U) {D F : U ⟶ E}
    (a : SSet.Homotopy D F) :
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy a)).map ((pre j).app E) =
      SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp a j)) := by
  have hc : curry a.h ≫ (pre j).app E = curry ((j ▷ (Δ[1] : SSet.{u})) ≫ a.h) := by
    apply uncurry_injective
    rw [uncurry_pre_app, uncurry_curry, uncurry_curry]
  apply SSet.Edge.ext
  change ((pre j).app E).app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (curry a.h)) =
    SSet.yonedaEquiv (curry ((j ▷ (Δ[1] : SSet.{u})) ≫ a.h))
  rw [← SSet.yonedaEquiv_comp, hc]

/-- 二脚が変わるホーン族は、全パラメータの前合成と厳密に可換。 -/
lemma varyingKanSpanHornFamily_naturality {T U E : SSet.{u}} (j : T ⟶ U)
    {D F G : U ⟶ E} (a : SSet.Homotopy D F) (b : SSet.Homotopy D G) :
    ((horn 2 (0 : Fin 3) : SSet.{u}) ◁ j) ≫ varyingKanSpanHornFamily a b =
      varyingKanSpanHornFamily (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp a j) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp b j) := by
  rw [varyingKanSpanHornFamily, BraidedCategory.braiding_naturality_right_assoc,
    ← uncurry_pre_app, kanSpanHorn_postcomp,
    varyingKanSpanEdge_precomp, varyingKanSpanEdge_precomp]
  rfl

end SerrePositivity.KST.SConstruction
