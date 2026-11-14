module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianEdgeInterchange

/-! # 直積族の指定辺の評価と移送
概要：直積の因子を移送してから評価する辺を、評価後に写す辺と同定する。
方針：族の射の等号を同じ一単体で評価する。
規約：辺の始点・終点の表示によらず、同じ一単体を保持する。
使われ方：因子三角形・交差正方形・自然性の分解三角形の共有辺の照合。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial

/-- 任意の族の可換式は、指定辺の実際の一単体で可換する。 -/
lemma mappedEdge_square {A B C D : SSet.{u}}
    (p : A ⟶ B) (F : A ⟶ C) (G : B ⟶ D) (q : C ⟶ D)
    (h : p ≫ G = F ≫ q) {x y : A _⦋0⦌} (e : A.Edge x y) :
    ((e.map p).map G).edge = ((e.map F).map q).edge :=
  ConcreteCategory.congr_hom (NatTrans.congr_app h (Opposite.op ⦋1⦌)) e.edge

/-- 第二因子を移送する可換式は、第一因子を固定した指定辺でも可換する。 -/
lemma cartesianLeftFamilyEdge_square {K A B C D : SSet.{u}}
    (p : A ⟶ B) (F : K ⊗ A ⟶ C) (G : K ⊗ B ⟶ D) (q : C ⟶ D)
    (h : (𝟙 K ⊗ₘ p) ≫ G = F ≫ q)
    (k : K _⦋0⦌) {x y : A _⦋0⦌} (e : A.Edge x y) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair (.id k) (e.map p)).map G).edge =
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair (.id k) e).map F).map q).edge :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.mappedEdge_square (𝟙 K ⊗ₘ p) F G q h (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair (.id k) e)

/-- 第一因子を移送する可換式は、第二因子を固定した指定辺でも可換する。 -/
lemma cartesianRightFamilyEdge_square {K A B C D : SSet.{u}}
    (p : A ⟶ B) (F : A ⊗ K ⟶ C) (G : B ⊗ K ⟶ D) (q : C ⟶ D)
    (h : (p ⊗ₘ 𝟙 K) ≫ G = F ≫ q)
    (k : K _⦋0⦌) {x y : A _⦋0⦌} (e : A.Edge x y) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair (e.map p) (.id k)).map G).edge =
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair e (.id k)).map F).map q).edge :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.mappedEdge_square (p ⊗ₘ 𝟙 K) F G q h (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair e (.id k))

/-- 第一因子の固定頂点を移すことと、直積族へ前合成することは同じ辺を与える。 -/
lemma cartesianLeftFamilyEdge_parameter {K K' A M : SSet.{u}}
    (p : K ⟶ K') (F : K' ⊗ A ⟶ M) (k : K _⦋0⦌)
    {x y : A _⦋0⦌} (e : A.Edge x y) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair (.id (p.app _ k)) e).map F).edge =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair (.id k) e).map ((p ⊗ₘ 𝟙 A) ≫ F)).edge := by
  change F.app (Opposite.op ⦋1⦌) (K'.σ 0 (p.app _ k), e.edge) =
    F.app (Opposite.op ⦋1⦌) (p.app _ (K.σ 0 k), e.edge)
  exact congrArg (fun z => F.app (Opposite.op ⦋1⦌) (z, e.edge))
    (ConcreteCategory.congr_hom (p.naturality (SimplexCategory.σ (0 : Fin 1)).op) k).symm

/-- 第二因子の固定頂点を移すことと、直積族へ前合成することは同じ辺を与える。 -/
lemma cartesianRightFamilyEdge_parameter {K K' A M : SSet.{u}}
    (p : K ⟶ K') (F : A ⊗ K' ⟶ M) (k : K _⦋0⦌)
    {x y : A _⦋0⦌} (e : A.Edge x y) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair e (.id (p.app _ k))).map F).edge =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair e (.id k)).map ((𝟙 A ⊗ₘ p) ≫ F)).edge := by
  change F.app (Opposite.op ⦋1⦌) (e.edge, K'.σ 0 (p.app _ k)) =
    F.app (Opposite.op ⦋1⦌) (e.edge, p.app _ (K.σ 0 k))
  exact congrArg (fun z => F.app (Opposite.op ⦋1⦌) (e.edge, z))
    (ConcreteCategory.congr_hom (p.naturality (SimplexCategory.σ (0 : Fin 1)).op) k).symm

/-- 第二因子の辺の移送は直積族への前合成である。 -/
lemma cartesianLeftFamilyEdge_moving {K A B M : SSet.{u}}
    (p : A ⟶ B) (F : K ⊗ B ⟶ M) (k : K _⦋0⦌)
    {x y : A _⦋0⦌} (e : A.Edge x y) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair (.id k) (e.map p)).map F).edge =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair (.id k) e).map ((𝟙 K ⊗ₘ p) ≫ F)).edge := rfl

/-- 第一因子の辺の移送は直積族への前合成である。 -/
lemma cartesianRightFamilyEdge_moving {K A B M : SSet.{u}}
    (p : A ⟶ B) (F : B ⊗ K ⟶ M) (k : K _⦋0⦌)
    {x y : A _⦋0⦌} (e : A.Edge x y) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair (e.map p) (.id k)).map F).edge =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair e (.id k)).map ((p ⊗ₘ 𝟙 K) ≫ F)).edge := rfl

/-- 同じ単体を評価した族の射の等号は、実際の辺の一単体を保つ。 -/
lemma mappedEdge_family_congr {A B : SSet.{u}} (F G : A ⟶ B) (h : F = G)
    {x y : A _⦋0⦌} (e : A.Edge x y) : (e.map F).edge = (e.map G).edge :=
  ConcreteCategory.congr_hom (NatTrans.congr_app h (Opposite.op ⦋1⦌)) e.edge

/-- 第二因子の一単体を同じものへ置き換えても、固定第一因子との評価辺は変わらない。 -/
lemma cartesianLeftFamilyEdge_congr {K L M : SSet.{u}} (F : K ⊗ L ⟶ M)
    (k : K _⦋0⦌) {x₀ x₁ y₀ y₁ : L _⦋0⦌}
    (e : L.Edge x₀ x₁) (f : L.Edge y₀ y₁) (h : e.edge = f.edge) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair (.id k) e).map F).edge =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair (.id k) f).map F).edge :=
  congrArg (fun z => F.app (Opposite.op ⦋1⦌) ((SSet.Edge.id k).edge, z)) h

/-- 第一因子の一単体を同じものへ置き換えても、固定第二因子との評価辺は変わらない。 -/
lemma cartesianRightFamilyEdge_congr {K L M : SSet.{u}} (F : L ⊗ K ⟶ M)
    (k : K _⦋0⦌) {x₀ x₁ y₀ y₁ : L _⦋0⦌}
    (e : L.Edge x₀ x₁) (f : L.Edge y₀ y₁) (h : e.edge = f.edge) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair e (.id k)).map F).edge =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair f (.id k)).map F).edge :=
  congrArg (fun z => F.app (Opposite.op ⦋1⦌) (z, (SSet.Edge.id k).edge)) h

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cartesianLeftFamilyEdge_congr := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cartesianLeftFamilyEdge_congr

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cartesianLeftFamilyEdge_moving := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cartesianLeftFamilyEdge_moving

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cartesianLeftFamilyEdge_parameter := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cartesianLeftFamilyEdge_parameter

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cartesianLeftFamilyEdge_square := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cartesianLeftFamilyEdge_square

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cartesianRightFamilyEdge_congr := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cartesianRightFamilyEdge_congr

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cartesianRightFamilyEdge_moving := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cartesianRightFamilyEdge_moving

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cartesianRightFamilyEdge_parameter := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cartesianRightFamilyEdge_parameter

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cartesianRightFamilyEdge_square := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cartesianRightFamilyEdge_square

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.mappedEdge_family_congr := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.mappedEdge_family_congr

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.mappedEdge_square := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.mappedEdge_square
