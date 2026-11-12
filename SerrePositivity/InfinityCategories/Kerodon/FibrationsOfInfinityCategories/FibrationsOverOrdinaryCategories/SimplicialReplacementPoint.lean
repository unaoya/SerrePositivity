module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementAssembly
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementFiber

/-!
概要：一点の順序圏上の simplicial replacement と係数値の厳密な同型。
方針：底の全射列が同じ定値射列であることを使い、係数単体の Yoneda 表示を戻す。
規約：底の対象の型と各 Hom は subsingleton、指定対象 c を用いる。
使われ方：Kerodon Example 5.3.2.2（Tag 035W）、1 単体上の simplicial replacement の写像円柱表示。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：一点の薄い圏への射列は任意の指定対象の定値射列と等しい。
方針：頂点の一意性と Hom の一意性から関手の外延性を使う。
規約：対象 c の存在を入力として受け取る。
使われ方：Kerodon Example 5.3.2.2（Tag 035W）、一点の底の単体の計算。 -/
lemma simplexChain_eq_constant {C : Type u} [Category.{u} C] [Subsingleton C]
    [Quiver.IsThin C] (c : C) {n : ℕ} (σ : ComposableArrows C n) :
    σ = (CategoryTheory.Functor.const (Fin (n + 1))).obj c :=
  CategoryTheory.Functor.ext (fun _ ↦ Subsingleton.elim _ _)
    (fun _ _ _ ↦ Subsingleton.elim _ _)

/-- 概要：一点の薄い圏上では係数値の定値包含が全空間との同型となる。
方針：各次数で底の射列を定値に書き換え、係数の Yoneda の全単射を使う。
規約：係数の Kan 性は不要。
使われ方：Kerodon Example 5.3.2.2（Tag 035W）、末尾が一点となる pushout の簡約。 -/
instance simplicialReplacementConstantLift_isIso
    {C : Type u} [Category.{u} C] [Subsingleton C] [Quiver.IsThin C]
    (F : C ⥤ SSet.{u}) (c : C) : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementConstantLift F c) := by
  rw [NatTrans.isIso_iff_isIso_app]
  rintro ⟨⟨n⟩⟩
  rw [isIso_iff_bijective]
  constructor
  · intro s t h
    exact SSet.yonedaEquiv.symm.injective (eq_of_heq (Sigma.mk.inj h).2)
  · rintro ⟨σ, τ⟩
    have hσ := simplexChain_eq_constant c σ
    subst σ
    refine ⟨SSet.yonedaEquiv τ, ?_⟩
    refine Sigma.ext (by rfl) ?_
    exact heq_of_eq (SSet.yonedaEquiv.symm_apply_apply τ)

/-- 概要：一点の薄い圏の nerve との直積からの第二射影は同型。
方針：各次数の底の射列の一意性を使って第二成分を一意に持ち上げる。
規約：c は底の一点の存在を与える。
使われ方：Kerodon Example 5.3.2.2（Tag 035W）、写像円柱の貼り合わせ部分の係数値への同定。 -/
lemma nervePoint_snd_isIso {C : Type u} [Category.{u} C] [Subsingleton C]
    [Quiver.IsThin C] (c : C) (K : SSet.{u}) : IsIso (snd (nerve C) K) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro d
  rw [isIso_iff_bijective]
  constructor
  · rintro ⟨σ, s⟩ ⟨τ, t⟩ h
    exact Prod.ext ((simplexChain_eq_constant c σ).trans
      (simplexChain_eq_constant c τ).symm) h
  · intro s
    exact ⟨((CategoryTheory.Functor.const (Fin (d.unop.len + 1))).obj c, s), rfl⟩

/-- 概要：一点の薄い圏上の組み立て射は唯一の係数変換と定値包含の合成。
方針：底の射列を定値へ書き換え、Yoneda の後合成自然性で係数単体を比較する。
規約：定値係数 K から F への自然変換 η は任意。
使われ方：Kerodon Example 5.3.2.2（Tag 035W）、写像円柱の端点の貼り合わせ射の計算。 -/
lemma simplicialReplacementAssembly_point
    {C : Type u} [Category.{u} C] [Subsingleton C] [Quiver.IsThin C]
    (c : C) {K : SSet.{u}} {F : C ⥤ SSet.{u}}
    (η : (CategoryTheory.Functor.const C).obj K ⟶ F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementAssembly η = snd (nerve C) K ≫ η.app c ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementConstantLift F c := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, s⟩
  have hσ := simplexChain_eq_constant c σ
  subst σ
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  exact SSet.yonedaEquiv_symm_comp s (η.app c)

/-- 概要：一点の薄い圏の nerve を標的とする射の fiber 包含は同型。
方針：各次数で底の単体が指定した頂点の定値単体と等しいことを使う。
規約：元の射の充填性は不要。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、底が一点のときの fiber と全空間の一致。 -/
lemma vertexFiberι_isIso_of_nervePoint
    {C : Type u} [Category.{u} C] [Subsingleton C] [Quiver.IsThin C]
    {E : SSet.{u}} (p : E ⟶ nerve C) (c : C) : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro d
  rw [isIso_iff_bijective]
  refine ⟨Subtype.val_injective, ?_⟩
  intro e
  refine ⟨⟨e, ?_⟩, rfl⟩
  exact simplexChain_eq_constant c (p.app d e)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
