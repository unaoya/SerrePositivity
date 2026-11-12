module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaUnitComponent
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFiberExtension

/-!
概要：comma の頂点が表す矢印を両端固定の区間写像空間の族として取り出す。
方針：定値族の標的を正規化し、ホモトピーを区間の curry で表示する。
規約：選んだ代表の射を保ち、ホモトピー類だけの対応にしない。
使われ方：単位比較の導来 fiber の指定点の族。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：comma fiber の頂点の Y 内での標的。
方針：fiber の包含と標的射影を零次元で評価する。
規約：始域 x は固定。
使われ方：区間写像空間の終点。 -/
noncomputable def unitCommaFiberTargetVertex {X Y : SSet.{u}} (G : Y ⟶ X)
    (x : X _⦋0⦌) (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌) : Y _⦋0⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget G).app (Opposite.op ⦋0⦌) v.val

/-- 概要：comma 頂点の定値族の標的は標的頂点に定値。
方針：定値射の後合成を二度計算する。
規約：パラメータは任意。
使われ方：正方形の側辺の端点の正規化。 -/
lemma unitCommaFiberTarget_const {A X Y : SSet.{u}} {G : Y ⟶ X} {x : X _⦋0⦌}
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTarget (SSet.const v : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) =
      SSet.const (unitCommaFiberTargetVertex G x v) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTarget, SSet.const_comp, SSet.const_comp]
  rfl

/-- 概要：comma 頂点の矢印の定値族の端点を x と G(y) で表示する。
方針：fiber のホモトピーの射を保ち、標的の定値公式で終点を揃える。
規約：新しいホモトピー代表を選ばない。
使われ方：区間写像空間の族への curry。 -/
noncomputable def unitCommaVertexHomotopy {X Y : SSet.{u}} (G : Y ⟶ X)
    (x : X _⦋0⦌) (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌) (A : SSet.{u}) :
    SSet.Homotopy (SSet.const x : A ⟶ X)
      (SSet.const (G.app (Opposite.op ⦋0⦌) (unitCommaFiberTargetVertex G x v))) where
  h := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy (SSet.const v : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x)).h
  h₀ := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy (SSet.const v : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x)).h₀
  h₁ := by
    have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy (SSet.const v : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x)).h₁
    change SSet.ι₁ ≫ _ = _ at h ⊢
    exact h.trans ((congrArg (fun f : A ⟶ Y ↦ f ≫ G)
      (unitCommaFiberTarget_const (A := A) v)).trans (SSet.const_comp _ G))
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

/-- 概要：comma 頂点の矢印を区間写像空間の族として表示する。
方針：元の矢印のホモトピーの区間を第一因子へ移して curry する。
規約：パラメータ A は任意。
使われ方：単位比較の導来 fiber の指定点の表示。 -/
noncomputable def unitCommaArrowFamily {X Y : SSet.{u}} (G : Y ⟶ X)
    (x : X _⦋0⦌) (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌) (A : SSet.{u}) :
    A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x (G.app (Opposite.op ⦋0⦌) (unitCommaFiberTargetVertex G x v)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyCurry ((β_ (Δ[1] : SSet.{u}) A).hom ≫ (unitCommaVertexHomotopy G x v A).h)
    (by
      rw [← Category.assoc]
      change SSet.ι₀ ≫ (unitCommaVertexHomotopy G x v A).h = _
      exact (unitCommaVertexHomotopy G x v A).h₀)
    (by
      rw [← Category.assoc]
      change SSet.ι₁ ≫ (unitCommaVertexHomotopy G x v A).h = _
      exact (unitCommaVertexHomotopy G x v A).h₁)

/-- 概要：矢印の区間族のホモトピー表示は元の頂点のホモトピー。
方針：curry の両逆と区間交換の二重適用を消す。
規約：厳密なホモトピーの等式。
使われ方：comma の右辺の h Fun の類を指定点の族と照合する。 -/
lemma unitCommaArrowFamily_homotopy {X Y : SSet.{u}} (G : Y ⟶ X)
    (x : X _⦋0⦌) (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌) (A : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy (unitCommaArrowFamily G x v A) = unitCommaVertexHomotopy G x v A := by
  apply RelativeMorphism.Homotopy.ext
  change (β_ A (Δ[1] : SSet.{u})).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry _ = _
  rw [unitCommaArrowFamily, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyUncurry_curry]
  simp only [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]

/-- 概要：comma の矢印の定値族の区間表示はパラメータ前合成に自然。
方針：fiber のホモトピーの前合成と区間交換の自然性を使う。
規約：頂点は固定し、パラメータの射は任意。
使われ方：矢印の区間族が一つの指定点への定値族であることの証明。 -/
lemma unitCommaArrowFamily_precomp {A B X Y : SSet.{u}} (G : Y ⟶ X)
    (x : X _⦋0⦌) (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌) (i : A ⟶ B) :
    i ≫ unitCommaArrowFamily G x v B = unitCommaArrowFamily G x v A := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]
  simp only [unitCommaArrowFamily, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyUncurry_curry]
  have h : (unitCommaVertexHomotopy G x v A).h =
      (i ▷ (Δ[1] : SSet.{u})) ≫ (unitCommaVertexHomotopy G x v B).h := by
    have hc : i ≫ (SSet.const v : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) = SSet.const v := SSet.comp_const _ _
    exact (congrArg (fun f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy f).h) hc).symm.trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy_precomp i (SSet.const v))
  rw [h]
  have hb : (Δ[1] : SSet.{u}) ◁ i ≫ (β_ (Δ[1] : SSet.{u}) B).hom =
      (β_ (Δ[1] : SSet.{u}) A).hom ≫ (i ▷ (Δ[1] : SSet.{u})) := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  rw [← Category.assoc, hb, Category.assoc]

/-- 概要：comma の頂点が表す区間写像空間の指定点。
方針：零単体パラメータの矢印の族を Yoneda の同値で読む。
規約：右辺のホモトピー代表を保持する。
使われ方：単位比較の導来 fiber を取る頂点。 -/
noncomputable def unitCommaArrowVertex {X Y : SSet.{u}} (G : Y ⟶ X)
    (x : X _⦋0⦌) (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x (G.app (Opposite.op ⦋0⦌) (unitCommaFiberTargetVertex G x v))) _⦋0⦌ :=
  SSet.yonedaEquiv (unitCommaArrowFamily G x v (Δ[0] : SSet.{u}))

/-- 概要：comma 頂点の矢印の族は指定点への定値射。
方針：点への定値射での前合成自然性と Yoneda 表示を使う。
規約：任意のパラメータ。
使われ方：比較の終点を厳密な頂点 fiber に固定する。 -/
lemma unitCommaArrowFamily_eq_const {X Y : SSet.{u}} (G : Y ⟶ X)
    (x : X _⦋0⦌) (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌) (A : SSet.{u}) :
    unitCommaArrowFamily G x v A = SSet.const (unitCommaArrowVertex G x v) := by
  rw [← unitCommaArrowFamily_precomp G x v
    (SSet.const (stdSimplex.obj₀Equiv.symm 0) : A ⟶ Δ[0]), SSet.const_comp]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
