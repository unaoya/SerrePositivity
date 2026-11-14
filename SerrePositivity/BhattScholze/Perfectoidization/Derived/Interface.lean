module
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.RingCompletion

public import SerrePositivity.CommutativeAlgebra.Perfectoid.Defs
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Basic
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.DiscreteEmbedding
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.HomotopyCategoryComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.HomotopyNatTrans
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.IntegralPerfectoid
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.Comparisons
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionMonoidal
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalMap
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.Pullback
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# 導来 perfectoid 化の構造と性質（BS 著者版 Definition 8.2）

## 概要
添字圏、導来対象・辺・自然変換、導来完備化 H⁰ の包装、単位付き導来極限錐のデータ、excision 図式、導来 perfectoid 化の構造体。

## 方針
D(R) 上の導来 perfectoid 化の性質を欄として束ねる（BS 著者版 Definition 8.2、
Proposition 8.5、Corollary 8.14、Theorem 10.11、Corollary 8.12）。

## 規約
導来 perfectoid 化の存在の入力は `Inputs` の入口で与える。

## 使われ方
E3 から環の定理を導く橋（IntegralExistence・Excision）、EInfinity の CAlg 版。
-/

universe u

/-! ## Perfectoid 化界面の通常の添字圏

概要：同じ宇宙の可換代数、導来 p 完備な代数、perfectoid 標的の圏を定める。
方針：可換環の under 圏と充満部分圏を用いる。
規約：台環は Type u、圏の対象は Type (u+1)。巨大極限の存在は要求しない。
使われ方：E3 界面の始域と BS 著者版 Proposition 8.5 の制限した添字圏。
-/

@[expose] public section Setup

namespace SerrePositivity.BhattScholze.PerfectoidizationInterface
open CategoryTheory
open SerrePositivity.DerivedCompletion

/-- Type u の通常の可換 R 代数の圏。構造射をデータとして保持する。 -/
abbrev A_R (R : Type u) [CommRing R] := Under (CommRingCat.of R)

/-- 通常の R 代数を、元の代数構造の射とともに束ねる。 -/
def ofAlgebra (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] : A_R R :=
  Under.mk (CommRingCat.ofHom (algebraMap R S))

/-- 始域に課す導来 p 完備性。通常の p 進完備性へ置き換えない。 -/
def completeProperty (R : Type u) [CommRing R] (p : ℕ) : ObjectProperty (A_R R) :=
  fun S => IsModuleComplete S.right (p : S.right) (ModuleCat.of S.right S.right)

/-- 導来 p 完備な通常の R 代数の充満部分圏。 -/
abbrev C_R (R : Type u) [CommRing R] (p : ℕ) := (completeProperty R p).FullSubcategory

/-- 完備性の条件だけを忘れる包含関手。 -/
abbrev completeInclusion (R : Type u) [CommRing R] (p : ℕ) : C_R R p ⥤ A_R R :=
  (completeProperty R p).ι

/-- S の下の環のうち、標的が perfectoid であるという性質。 -/
def perfectoidTargetProperty (p : ℕ) [Fact p.Prime] (S : CommRingCat.{u}) :
    ObjectProperty (Under S) := fun T => IsIntegralPerfectoid T.right p

/-- Type u の perfectoid 標的 S → T の圏。射の向きを反転しない。 -/
abbrev PerfUnder_u (p : ℕ) [Fact p.Prime] (S : CommRingCat.{u}) :=
  (perfectoidTargetProperty p S).FullSubcategory

/-- perfectoid 条件を忘れ、元の S 上の環を取り出す。 -/
abbrev perfectoidTargetInclusion (p : ℕ) [Fact p.Prime] (S : CommRingCat.{u}) :
    PerfUnder_u p S ⥤ Under S := (perfectoidTargetProperty p S).ι

/-- perfectoid 標的の R 作用は R → S → T の合成で定める。 -/
def targetAlgebra (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (S : A_R R) :
    PerfUnder_u p S.right ⥤ A_R R :=
  perfectoidTargetInclusion p S.right ⋙ Under.map S.hom

/-- 通常の代数圏の nerve。対象宇宙 u+1 に置く。 -/
abbrev algebraNerve (R : Type u) [CommRing R] : SSet.{u + 1} := nerve (A_R R)

/-- 制限した perfectoid 標的圏の nerve。 -/
abbrev perfectoidTargetNerve (p : ℕ) [Fact p.Prime] (S : CommRingCat.{u}) : SSet.{u + 1} :=
  nerve (PerfUnder_u p S)

end SerrePositivity.BhattScholze.PerfectoidizationInterface

end Setup

/-! ## 界面で用いる導来対象・辺・自然変換

概要：D5b の離散埋め込みと D3 の同値を界面の名前空間へ包装する。
方針：頂点・辺を評価し、整数次数のコホモロジーを通常の導来圏で取る。
規約：自然変換は区間との積からの単体的射である。
使われ方：E3 の単位、H⁰ の環構造、制限した標的図式。
-/

@[expose] public noncomputable section Derived

namespace SerrePositivity.BhattScholze.PerfectoidizationInterface
open CategoryTheory CategoryTheory.Limits MonoidalCategory DifferentialGraded
open SerrePositivity.InfinityCategories
open scoped Simplicial
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- D5b の離散可換代数の埋め込みを、同じ under 圏の始域で使う。 -/
abbrev J : algebraNerve R ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteEmbedding R

/-- 単体的関手の通常の代数における値。 -/
def vertex (F : algebraNerve R ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R) (S : A_R R) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R) _⦋0⦌ := F.app _ (ComposableArrows.mk₀ S)

/-- 通常の代数の射を単体的関手で写した辺。 -/
def edge (F : algebraNerve R ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R) {S T : A_R R} (f : S ⟶ T) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R).Edge (vertex R F S) (vertex R F T) :=
  (CategoryTheory.nerve.edgeMk f).map F

/-- D3 経由の整数次数コホモロジー関手。 -/
def HFunctor (i : ℤ) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyCategory R ⥤ ModuleCat.{u} R :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalence R).functor ⋙ DerivedCategory.homologyFunctor _ i

/-- 導来頂点の i 次コホモロジー加群。 -/
def H (i : ℤ) (x : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R) _⦋0⦌) : ModuleCat.{u} R :=
  (HFunctor R i).obj ⟨x⟩

/-- 導来辺がコホモロジー上に誘導する線形射。 -/
def HMap (i : ℤ) {x y : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R) _⦋0⦌}
    (e : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R).Edge x y) : H R i x ⟶ H R i y :=
  (HFunctor R i).map (SSet.Truncated.HomotopyCategory₂.homMk e.toTruncated)

/-- D3 によるコホモロジーは、頂点の semifree 複体のコホモロジーに一致する。 -/
def HIso (i : ℤ) (x : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R) _⦋0⦌) :
    H R i x ≅ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategoryVertexEquiv R x).val.homology i :=
  (DerivedCategory.homologyFunctorFactorsh (ModuleCat R) i).app
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeHomotopyComparison R).obj ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityH0Equivalence R).functor.obj ⟨x⟩)) ≪≫
    (HomotopyCategory.homologyFunctorFactors (ModuleCat R) (.up ℤ) i).app
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategoryVertexEquiv R x).val

/-- 離散埋め込みの零次コホモロジーは元の R 加群。 -/
def JHZeroIso (S : A_R R) :
    H R 0 (vertex R (J R) S) ≅ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteAlgebraModule R).obj S :=
  HIso R 0 _ ≪≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteEmbeddingHomologyZeroIso R S

/-- 離散性は零次以外の全コホモロジーの消滅。 -/
def Disc (x : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R) _⦋0⦌) : Prop :=
  ∀ i : ℤ, i ≠ 0 → IsZero (H R i x)

/-- 単体的自然変換。両端の等式もデータに含む。 -/
abbrev NatInfinity (F G : algebraNerve R ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R) := SSet.Homotopy F G

/-- 自然変換の S における成分の辺。 -/
def component {F G : algebraNerve R ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R}
    (η : NatInfinity R F G) (S : A_R R) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R).Edge (vertex R F S) (vertex R G S) :=
  (SSet.Edge.ofTruncated
    (((SSet.Truncated.Edge.id (X := (SSet.truncation 2).obj (algebraNerve R))
      (ComposableArrows.mk₀ S)).tensor _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge).map
        ((SSet.truncation 2).map η.h))).ofEq
    (congrArg (fun (f : algebraNerve R ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R) =>
      f.app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ S)) η.h₀)
    (congrArg (fun (f : algebraNerve R ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R) =>
      f.app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ S)) η.h₁)

/-- 指定された perfectoid 標的への離散 R 代数の図式。 -/
def targetDiagram (p : ℕ) [Fact p.Prime] (S : A_R R) :
    perfectoidTargetNerve p S.right ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R :=
  nerveMap (targetAlgebra R p S) ≫ J R

end SerrePositivity.BhattScholze.PerfectoidizationInterface

end Derived

/-! ## 通常の代数への導来完備化 H⁰ の包装

概要：実際の一変数 Koszul 完備化 H⁰ を環の関手にする。
方針：既存の単位と完備標的への環準同型の一意延長を用いる。
規約：通常の完備化との一致や有界 p 冪ねじれを仮定しない。
使われ方：非完備な始域の拡張と perfectoid 標的の添字圏の同値。
-/

@[expose] public noncomputable section Completion

namespace SerrePositivity.BhattScholze.PerfectoidizationInterface
open CategoryTheory
open SerrePositivity.DerivedCompletion
open SerrePositivity.InfinityCategories
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (p : ℕ)

/-- 完備化 H⁰ の環自身も導来 p 完備である。 -/
theorem completionRing_complete (S : CommRingCat.{u}) :
    IsModuleComplete (completionRing p S) (p : completionRing p S)
      (ModuleCat.of (completionRing p S) (completionRing p S)) := by
  letI := (completionUnit p S).hom.toAlgebra
  have h : IsModuleComplete S (p : S) (ModuleCat.of S (completionRing p S)) :=
    principalCompletion_isModuleComplete_unit (p : S)
  have h' := (isModuleComplete_algebraMap_iff S (completionRing p S)
    (p : S) (completionRing p S)).mpr h
  simpa only [map_natCast] using h'

/-- 選んだ延長は元の単位との図式を満たす。 -/
@[simp] theorem completionLift_comp {S T : CommRingCat.{u}} (f : S ⟶ T)
    (hT : IsModuleComplete T (p : T) (ModuleCat.of T T)) :
    completionUnit p S ≫ completionLift p f hT = f :=
  (completion_existsUnique p f hT).choose_spec.1

/-- 環の射が誘導する H⁰ 完備化の射。 -/
def completionMap {S T : CommRingCat.{u}} (f : S ⟶ T) :
    completionRing p S ⟶ completionRing p T :=
  completionLift p (f ≫ completionUnit p T) (completionRing_complete p T)

/-- 誘導射は元の二つの単位と両立する。 -/
@[simp] theorem completionMap_comp {S T : CommRingCat.{u}} (f : S ⟶ T) :
    completionUnit p S ≫ completionMap p f = f ≫ completionUnit p T :=
  completionLift_comp p _ _

/-- 完備化の射は恒等射を保つ。 -/
@[simp] theorem completionMap_id (S : CommRingCat.{u}) : completionMap p (𝟙 S) = 𝟙 _ := by
  apply completion_hom_ext p (completionRing_complete p S)
  simp

/-- 完備化の射は合成を保つ。 -/
@[simp] theorem completionMap_comp_map {S T U : CommRingCat.{u}} (f : S ⟶ T) (g : T ⟶ U) :
    completionMap p (f ≫ g) = completionMap p f ≫ completionMap p g := by
  apply completion_hom_ext p (completionRing_complete p U)
  rw [completionMap_comp, ← Category.assoc, completionMap_comp,
    Category.assoc, Category.assoc, completionMap_comp]

/-- 通常の可換環上の導来完備化 H⁰ 関手。 -/
def ringCompletionFunctor : CommRingCat.{u} ⥤ CommRingCat.{u} where
  obj := completionRing p
  map := completionMap p
  map_id := completionMap_id p
  map_comp := completionMap_comp_map p

/-- 元の環が既に導来 p 完備なら、指定された単位は同型。 -/
def completionUnitIso (S : CommRingCat.{u})
    (hS : IsModuleComplete S (p : S) (ModuleCat.of S S)) : S ≅ completionRing p S where
  hom := completionUnit p S
  inv := completionLift p (𝟙 S) hS
  hom_inv_id := completionLift_comp p _ hS
  inv_hom_id := by
    apply completion_hom_ext p (completionRing_complete p S)
    simp [← Category.assoc]

/-- R 作用を元の構造射と完備化単位の合成に固定した H⁰ 完備化関手。 -/
def completionFunctor (R : Type u) [CommRing R] : A_R R ⥤ A_R R where
  obj S := Under.mk (S.hom ≫ completionUnit p S.right)
  map f := Under.homMk (completionMap p f.right) (by
    dsimp only [Under.mk_hom]
    rw [Category.assoc, completionMap_comp, ← Category.assoc, Under.w])
  map_id S := by ext1; exact completionMap_id p S.right
  map_comp f g := by ext1; exact completionMap_comp_map p f.right g.right

/-- 代数の H⁰ 完備化単位は、元の R 作用を保持する自然変換。 -/
def completionAlgebraUnit (R : Type u) [CommRing R] : 𝟭 (A_R R) ⟶ completionFunctor p R where
  app S := Under.homMk (completionUnit p S.right) rfl
  naturality := by intro S T f; ext1; exact (completionMap_comp p f.right).symm

/-- 完備代数上では、指定した代数の単位も同型になる。 -/
def completionAlgebraUnitIso (R : Type u) [CommRing R] (S : C_R R p) :
    S.obj ≅ (completionFunctor p R).obj S.obj :=
  Under.isoMk (completionUnitIso p S.obj.right S.property) rfl

variable [Fact p.Prime]

/-- 完備化の単位で前合成する、perfectoid 標的の制限関手。 -/
def targetRestriction (S : CommRingCat.{u}) :
    PerfUnder_u p (completionRing p S) ⥤ PerfUnder_u p S where
  obj T := ⟨(Under.map (completionUnit p S)).obj T.obj, T.property⟩
  map f := ObjectProperty.homMk ((Under.map (completionUnit p S)).map f.hom)

/-- perfectoid 標的への単位付き一意延長で作る逆向きの関手。 -/
def targetExtension (S : CommRingCat.{u}) :
    PerfUnder_u p S ⥤ PerfUnder_u p (completionRing p S) where
  obj T := ⟨Under.mk (completionLift p T.obj.hom (T.property.isModuleComplete T.obj.right p)),
    T.property⟩
  map {T U} f := ObjectProperty.homMk (Under.homMk f.hom.right (by
    dsimp only [Under.mk_hom]
    apply completion_hom_ext p (U.property.isModuleComplete U.obj.right p)
    rw [← Category.assoc, completionLift_comp, completionLift_comp]
    exact Under.w f.hom))
  map_id T := by ext1; ext1; rfl
  map_comp f g := by ext1; ext1; rfl

/-- Type u の全 perfectoid 標的の圏は H⁰ 完備化で変わらない。 -/
def completionTargetEquivalence (S : CommRingCat.{u}) :
    PerfUnder_u p (completionRing p S) ≌ PerfUnder_u p S where
  functor := targetRestriction p S
  inverse := targetExtension p S
  unitIso := NatIso.ofComponents (fun T => ObjectProperty.isoMk _
    (Under.isoMk (Iso.refl _) (by
      change T.obj.hom ≫ 𝟙 _ =
        completionLift p (completionUnit p S ≫ T.obj.hom)
          (T.property.isModuleComplete T.obj.right p)
      rw [Category.comp_id]
      apply completion_hom_ext p (T.property.isModuleComplete T.obj.right p)
      exact (completionLift_comp p (completionUnit p S ≫ T.obj.hom)
        (T.property.isModuleComplete T.obj.right p)).symm))) (by
          intro T U f
          ext1; ext1
          change f.hom.right ≫ 𝟙 _ = 𝟙 _ ≫ f.hom.right
          simp)
  counitIso := NatIso.ofComponents (fun T => ObjectProperty.isoMk _
    (Under.isoMk (Iso.refl _) (by
      change (completionUnit p S ≫ completionLift p T.obj.hom
        (T.property.isModuleComplete T.obj.right p)) ≫ 𝟙 _ = T.obj.hom
      rw [Category.comp_id, completionLift_comp]))) (by
        intro T U f
        ext1; ext1
        change f.hom.right ≫ 𝟙 _ = 𝟙 _ ≫ f.hom.right
        simp)
  functor_unitIso_comp := by
    intro T
    ext1; ext1
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    simp

/-- 添字の射に沿って join 錐を制限する。極限性を仮定しない。 -/
def restrictCone {K L X : SSet.{u + 1}} {F : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone F) (f : L ⟶ K) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (f ≫ F) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) f ≫ c.val, by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.assoc, c.property]⟩

/-- 添字を制限しても錐の指定頂点を保つ。 -/
theorem restrictCone_vertex {K L X : SSet.{u + 1}} {F : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone F) (f : L ⟶ K) : (restrictCone c f).vertex = c.vertex := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex_eq, restrictCone, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap,
    Category.id_comp]

/-- 制限関手で運んだ標的の R 作用は、完備化側で指定した作用と同じ。 -/
theorem targetRestriction_algebra (R : Type u) [CommRing R] (S : A_R R) :
    targetRestriction p S.right ⋙ targetAlgebra R p S =
      targetAlgebra R p ((completionFunctor p R).obj S) := by
  rfl

/-- 延長関手は完備化単位の図式により、元の標的の R 作用も保つ。 -/
theorem targetExtension_algebra (R : Type u) [CommRing R] (S : A_R R) :
    targetExtension p S.right ⋙ targetAlgebra R p ((completionFunctor p R).obj S) =
      targetAlgebra R p S := by
  refine CategoryTheory.Functor.ext (fun T => ?_) ?_
  · change Under.mk ((S.hom ≫ completionUnit p S.right) ≫ completionLift p T.obj.hom
        (T.property.isModuleComplete T.obj.right p)) = Under.mk (S.hom ≫ T.obj.hom)
    congr 1
    rw [Category.assoc, completionLift_comp]
  · intro T U f
    ext1
    simp [Under.eqToHom_right, targetExtension, targetAlgebra]

/-- 完備化側の図式は、元の図式の標的制限と一致する。 -/
theorem targetDiagram_restriction (R : Type u) [CommRing R] (S : A_R R) :
    nerveMap (targetRestriction p S.right) ≫ targetDiagram R p S =
      targetDiagram R p ((completionFunctor p R).obj S) := by
  have h := nerveFunctor.map_comp (targetRestriction p S.right).toCatHom
    (targetAlgebra R p S).toCatHom
  change nerveMap (targetRestriction p S.right ⋙ targetAlgebra R p S) =
    nerveMap (targetRestriction p S.right) ≫ nerveMap (targetAlgebra R p S) at h
  rw [targetDiagram, ← Category.assoc, ← h, targetRestriction_algebra]
  rfl

/-- 元の図式は、完備化側の図式の標的延長による制限と一致する。 -/
theorem targetDiagram_extension (R : Type u) [CommRing R] (S : A_R R) :
    nerveMap (targetExtension p S.right) ≫
        targetDiagram R p ((completionFunctor p R).obj S) = targetDiagram R p S := by
  have h := nerveFunctor.map_comp (targetExtension p S.right).toCatHom
    (targetAlgebra R p ((completionFunctor p R).obj S)).toCatHom
  change nerveMap (targetExtension p S.right ⋙
      targetAlgebra R p ((completionFunctor p R).obj S)) =
    nerveMap (targetExtension p S.right) ≫
      nerveMap (targetAlgebra R p ((completionFunctor p R).obj S)) at h
  rw [targetDiagram, ← Category.assoc, ← h, targetExtension_algebra]
  rfl

/-- 元の標的図式の指定錐を、完備化側の標的図式へ運ぶ。 -/
def completionRestrictCone (R : Type u) [CommRing R] (S : A_R R)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (targetDiagram R p S)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (targetDiagram R p ((completionFunctor p R).obj S)) :=
  (restrictCone c (nerveMap (targetRestriction p S.right))).cast (targetDiagram_restriction p R S)

/-- 完備化側の標的図式の指定錐を、元の標的図式へ運ぶ。 -/
def completionExtendCone (R : Type u) [CommRing R] (S : A_R R)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (targetDiagram R p ((completionFunctor p R).obj S))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (targetDiagram R p S) :=
  (restrictCone c (nerveMap (targetExtension p S.right))).cast (targetDiagram_extension p R S)

/-- 完備化側へ運んだ錐の頂点は元の頂点と同じ。 -/
theorem completionRestrictCone_vertex (R : Type u) [CommRing R] (S : A_R R)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (targetDiagram R p S)) : (completionRestrictCone p R S c).vertex = c.vertex := by
  rw [completionRestrictCone, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex_cast, restrictCone_vertex]

/-- 元の側へ運んだ錐の頂点も元の頂点と同じ。 -/
theorem completionExtendCone_vertex (R : Type u) [CommRing R] (S : A_R R)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (targetDiagram R p ((completionFunctor p R).obj S))) :
    (completionExtendCone p R S c).vertex = c.vertex := by
  rw [completionExtendCone, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex_cast, restrictCone_vertex]

end SerrePositivity.BhattScholze.PerfectoidizationInterface

end Completion

/-! ## H⁰ の環構造と単位付き導来極限錐のデータ

概要：底の導来対象と無関係な環構造を許さず、辺と射影の乗法整合性を記録する。
方針：通常の R 代数の関手と加群の比較同型を持ち、実際の join 錐の脚を照合する。
規約：単位との両立は図式上の slice の辺として保持する。
使われ方：E3 界面の h0 と limitCone の型。
-/

@[expose] public noncomputable section LimitData

namespace SerrePositivity.BhattScholze.PerfectoidizationInterface
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable (R : Type u) [CommRing R]

/-- H⁰ の環・辺・単位を、底の導来加群のデータに結び付ける。 -/
structure H0RingData (P : algebraNerve R ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R)
    (η : NatInfinity R (J R) P) where
  /-- H⁰ の通常の R 代数の関手。 -/
  ringFunctor : A_R R ⥤ A_R R
  /-- 元の加群構造との指定同型。 -/
  moduleIso : ∀ S, (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteAlgebraModule R).obj (ringFunctor.obj S) ≅ H R 0 (vertex R P S)
  /-- 代数の射の底は同じ辺の H⁰ と一致する。 -/
  map_compat : ∀ {S T} (f : S ⟶ T),
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteAlgebraModule R).map (ringFunctor.map f) ≫ (moduleIso T).hom =
      (moduleIso S).hom ≫ HMap R 0 (edge R P f)
  /-- H⁰ の環準同型としての自然な単位。 -/
  unit : 𝟭 (A_R R) ⟶ ringFunctor
  /-- 環の単位は、単体的単位の成分の H⁰ そのもの。 -/
  unit_compat : ∀ S,
    (JHZeroIso R S).hom ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteAlgebraModule R).map (unit.app S) ≫ (moduleIso S).hom =
      HMap R 0 (component R η S)

/-- join の左頂点から指定した右頂点へ向かう、一単体の標準表示。 -/
def joinLegSimplex {K : SSet.{u + 1}} (x : K _⦋0⦌) : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u + 1}) K) _⦋1⦌ :=
  ⟨⟨1, by decide⟩, SSet.yonedaEquiv (𝟙 Δ[0]), x⟩

/-- 指定された S → T を R 上の代数の射として使う。 -/
def targetUnitMap (p : ℕ) [Fact p.Prime] (S : A_R R) (T : PerfUnder_u p S.right) :
    S ⟶ (targetAlgebra R p S).obj T := Under.homMk T.obj.hom rfl

/-- S から perfectoid 標的への射は標的圏の射について自然。 -/
theorem targetUnitMap_naturality (p : ℕ) [Fact p.Prime] (S : A_R R)
    {T U : PerfUnder_u p S.right} (f : T ⟶ U) :
    targetUnitMap R p S T ≫ (targetAlgebra R p S).map f = targetUnitMap R p S U := by
  ext1
  exact Under.w f.hom

/-- BS 著者版 Proposition 8.5 の特定の錐と、単位・環の射影との整合性。極限性は別の欄で受け取る。 -/
structure BSLimitConeData (p : ℕ) [Fact p.Prime]
    (P : algebraNerve R ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R) (η : NatInfinity R (J R) P)
    (h0 : H0RingData R P η) (S : A_R R) where
  /-- Type u の標的だけを添字とする導来錐。 -/
  cone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (targetDiagram R p S)
  /-- 錐の頂点は指定された perfectoid 化。 -/
  vertex_eq : cone.vertex = vertex R P S
  /-- 通常の代数圏での、元の S から全標的への錐。 -/
  sourceCone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (nerveMap (targetAlgebra R p S))
  /-- 通常の錐の頂点を元の S に固定する。 -/
  source_vertex : sourceCone.vertex = ComposableArrows.mk₀ S
  /-- 通常の錐の各脚は元の S → T そのもの。nerve 内なので高次の合成もこれで固定される。 -/
  source_legs : ∀ T, sourceCone.val.app _ (joinLegSimplex (ComposableArrows.mk₀ T)) =
    ComposableArrows.mk₁ (targetUnitMap R p S T)
  /-- 図式上の錐の間の辺として単位による因子分解を保持する。 -/
  overSource : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (targetDiagram R p S)).Edge (sourceCone.postcomp (J R)) cone
  /-- その辺の頂点への射影は、元の単体的単位の成分。 -/
  overSource_unit : (overSource.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (targetDiagram R p S))).edge =
    (component R η S).edge
  /-- 実際の導来錐の脚を、両端を固定した辺として保持する。 -/
  projectionEdge : ∀ T : PerfUnder_u p S.right,
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R).Edge (vertex R P S) (vertex R (J R) ((targetAlgebra R p S).obj T))
  /-- 脚は任意に添えた辺でなく、join 錐の実際の一単体。 -/
  projectionEdge_eq : ∀ T, (projectionEdge T).edge =
    cone.val.app _ (joinLegSimplex (ComposableArrows.mk₀ T))
  /-- H⁰ 上の射影は環準同型である。 -/
  projection : ∀ T : PerfUnder_u p S.right, h0.ringFunctor.obj S ⟶ (targetAlgebra R p S).obj T
  /-- 各射影は元の単位との三角形を可換にする。 -/
  projection_unit : ∀ T, h0.unit.app S ≫ projection T = targetUnitMap R p S T
  /-- 環の射影は標的について自然。 -/
  projection_naturality : ∀ {T U : PerfUnder_u p S.right} (f : T ⟶ U),
    projection T ≫ (targetAlgebra R p S).map f = projection U
  /-- 射影の底の線形写像は、指定した導来錐の脚の H⁰ と一致する。 -/
  projection_compat : ∀ T,
    (h0.moduleIso S).hom ≫ HMap R 0 (projectionEdge T) ≫
        (JHZeroIso R ((targetAlgebra R p S).obj T)).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteAlgebraModule R).map (projection T)

end SerrePositivity.BhattScholze.PerfectoidizationInterface

end LimitData

/-! ## 通常の商図式からの単体的 excision 四角形

概要：元の四辺とその可換性を、二つの二単体として同時に保持する。
方針：通常の nerve の合成二単体を対角で貼り、単体的関手で写す。
規約：右下は通常の商 T/IT。導来テンソル積には置き換えない。
使われ方：E3 界面の excision 欄。
-/

@[expose] public noncomputable section ExcisionDiagram

namespace SerrePositivity.BhattScholze.PerfectoidizationInterface
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open SerrePositivity.InfinityCategories
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
variable (R : Type u) [CommRing R]

/-- 可換性の証明を共有する二つの合成二単体を、正方形へ貼り合わせる。 -/
def ordinarySquare {A B C D : A_R R} (a : A ⟶ B) (b : A ⟶ C)
    (c : B ⟶ D) (d : C ⟶ D) (w : a ≫ c = b ≫ d) :
    (Δ[1] : SSet.{u + 1}) ⊗ Δ[1] ⟶ algebraNerve R :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.desc
    (SSet.yonedaEquiv.symm (ComposableArrows.mk₂ b d))
    (SSet.yonedaEquiv.symm (ComposableArrows.mk₂ a c)) (by
      apply SSet.yonedaEquiv.injective
      change (nerve (A_R R)).δ 1 (ComposableArrows.mk₂ b d) =
        (nerve (A_R R)).δ 1 (ComposableArrows.mk₂ a c)
      rw [CategoryTheory.nerve.δ₁_mk₂_eq, CategoryTheory.nerve.δ₁_mk₂_eq, w])

/-- 四角形の上側の三角形は、元の左辺と下辺の合成二単体。 -/
theorem ordinarySquare_triangle_zero {A B C D : A_R R} (a : A ⟶ B) (b : A ⟶ C)
    (c : B ⟶ D) (d : C ⟶ D) (w : a ≫ c = b ≫ d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ ordinarySquare R a b c d w =
      SSet.yonedaEquiv.symm (ComposableArrows.mk₂ b d) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.inl_desc _ _ _

/-- 四角形の下側の三角形は、元の上辺と右辺の合成二単体。 -/
theorem ordinarySquare_triangle_one {A B C D : A_R R} (a : A ⟶ B) (b : A ⟶ C)
    (c : B ⟶ D) (d : C ⟶ D) (w : a ≫ c = b ≫ d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ ordinarySquare R a b c d w =
      SSet.yonedaEquiv.symm (ComposableArrows.mk₂ a c) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.inr_desc _ _ _

/-- 通常の商環に、元の構造射を通した R 作用を与える。 -/
def quotientAlgebra (S : A_R R) (I : Ideal S.right) : A_R R :=
  Under.mk (S.hom ≫ CommRingCat.ofHom (Ideal.Quotient.mk I))

/-- 元の通常の商環への射。 -/
def quotientProjection (S : A_R R) (I : Ideal S.right) : S ⟶ quotientAlgebra R S I :=
  Under.homMk (CommRingCat.ofHom (Ideal.Quotient.mk I)) rfl

/-- 下辺は、指定した f から誘導される通常の商の射。 -/
def quotientComparison {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right) :
    quotientAlgebra R S I ⟶ quotientAlgebra R T (I.map f.right.hom) :=
  Under.homMk (CommRingCat.ofHom (Ideal.quotientMap (I.map f.right.hom)
    f.right.hom Ideal.le_comap_map)) (by
      change (S.hom ≫ CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ _ = T.hom ≫ _
      rw [← Under.w f, Category.assoc, Category.assoc]
      congr 1)

/-- 四辺の可換性は、元の商の射と元の f についての等式。 -/
theorem quotientSquare_commutes {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right) :
    f ≫ quotientProjection R T (I.map f.right.hom) =
      quotientProjection R S I ≫ quotientComparison R f I := by
  ext1
  ext x
  rfl

/-- 通常の商による四角形を、可換性の二単体込みで P により写す。 -/
def perfdSquare (P : algebraNerve R ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R)
    {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right) :
    (Δ[1] : SSet.{u + 1}) ⊗ Δ[1] ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R :=
  ordinarySquare R f (quotientProjection R S I)
    (quotientProjection R T (I.map f.right.hom)) (quotientComparison R f I)
    (quotientSquare_commutes R f I) ≫ P

/-- perfectoid 化の四角形の一方の二単体は、元の二つの商の射の像。 -/
theorem perfdSquare_triangle_zero (P : algebraNerve R ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R)
    {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ perfdSquare R P f I =
      SSet.yonedaEquiv.symm (ComposableArrows.mk₂
        (quotientProjection R S I) (quotientComparison R f I)) ≫ P := by
  rw [perfdSquare, ← Category.assoc, ordinarySquare_triangle_zero]

/-- もう一方の二単体は、元の f と右側の商射の像。 -/
theorem perfdSquare_triangle_one (P : algebraNerve R ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R)
    {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ perfdSquare R P f I =
      SSet.yonedaEquiv.symm (ComposableArrows.mk₂ f
        (quotientProjection R T (I.map f.right.hom))) ≫ P := by
  rw [perfdSquare, ← Category.assoc, ordinarySquare_triangle_one]

/-- 既存 excision 入力と同じ階数1付値環への一意延長条件。 -/
def ArcOutside (p : ℕ) {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right) : Prop :=
  ∀ (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V],
    ringKrullDim V = 1 → IsAdicComplete (Ideal.span {(p : V)}) V →
    ∀ k : S.right →+* V, ¬ (I ≤ RingHom.ker k) →
      ∃! l : T.right →+* V, l.comp f.right.hom = k

end SerrePositivity.BhattScholze.PerfectoidizationInterface

end ExcisionDiagram

/-! ## D(R) 上の perfectoid 化界面（E3）の型

概要：原典の各性質を、その根拠を導出するためのデータとともに束ねる。
方針：界面の型だけを宣言し、存在は主張しない。
規約：普遍性は離散時の環準同型の普遍性。全射性や Tor 消滅を欄に含めない。
使われ方：Π2-5 以降で既存の二入力を界面依存の定理として導く。
-/

@[expose] public section Interface

namespace SerrePositivity.BhattScholze.PerfectoidizationInterface
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.InfinityCategories SerrePositivity.DerivedCompletion
open scoped Simplicial

/-- 原典と照合した E3 の型。界面の存在を追加の公理として宣言しない。 -/
structure PerfectoidizationInterfaceE3 (R : Type u) [CommRing R]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) where
  /-- 通常の R 代数の perfectoid 化を底の導来対象として受け取る（BS 著者版 Definition 8.2 に対応する E3 の欄。Lemma 8.4 とあわせて引用）。 -/
  perfd : algebraNerve R ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R
  /-- 元の離散代数からのホモトピー整合的な単位。 -/
  unit : NatInfinity R (J R) perfd
  /-- H⁰ の環構造と、単位・射のコホモロジーとの整合性。 -/
  h0 : H0RingData R perfd unit
  /-- 離散な場合だけ、指定した環の単位が perfectoid 化になる（BS 著者版 Corollary 8.14 の普遍性を、離散入力で値も離散の場合に受け取る E3 の欄）。 -/
  universal : ∀ S, Disc R (vertex R perfd S) →
    IsPerfectoidization p (h0.unit.app S).right.hom
  /-- Type u の標的を添字とする元の単位付きの指定錐を受け取る（BS 著者版 Proposition 8.5 の極限表示に使う E3 の欄）。 -/
  limitCone : ∀ S, BSLimitConeData R p perfd unit h0 S
  /-- 指定した錐の極限性。一般の巨大極限の存在は要求しない。 -/
  limit_isLimit : ∀ S, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (limitCone S).cone
  /-- 整代数の perfectoid 化の離散性と perfectoid 性を受け取る（BS 著者版 Theorem 10.11 の結論に対応する E3 の欄）。
  非完備な始域も含む。 -/
  integral : ∀ (S : A_R R),
    (letI : Algebra R S.right := S.hom.hom.toAlgebra; Algebra.IsIntegral R S.right) →
    Disc R (vertex R perfd S) ∧ IsIntegralPerfectoid (h0.ringFunctor.obj S).right p
  /-- 通常の商の指定四角形が、底の導来 ∞ 圏で引き戻しになる（BS 著者版 Corollary 8.12 の引き戻しを、離散入力について底の導来圏で受け取る E3 の欄）。 -/
  excision : ∀ {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right),
    IsModuleComplete S.right (p : S.right) (ModuleCat.of S.right S.right) →
    IsModuleComplete T.right (p : T.right) (ModuleCat.of T.right T.right) →
    IsModuleComplete S.right (p : S.right) (ModuleCat.of S.right I) →
    ArcOutside R p f I → _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (perfdSquare R perfd f I)

end SerrePositivity.BhattScholze.PerfectoidizationInterface

end Interface
