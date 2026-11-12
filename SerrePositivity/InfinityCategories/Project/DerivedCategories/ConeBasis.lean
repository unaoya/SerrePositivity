module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeBasisEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeBasisHeight
public import SerrePositivity.DifferentialGraded.Complexes.Cone
public import Mathlib.LinearAlgebra.Basis.Prod

/-! # 任意の鎖写像の cone の semibasis

概要：semifree 複体間の任意の射の cone に高さ付き基底を構成する。
方針：次数ごとの直積基底に始域側の付け直した高さと終域側の元の高さを使う。
規約：cone の次数 k は P の次数 k+1 と Q の次数 k。使われ方：無条件の cone 閉性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded CochainComplex HomologicalComplex
variable {S : Type u} [CommRing S] {P Q : Complex S} (f : P ⟶ Q)

/-- 概要：cone の各次数を始域の次の次数と終域の直積へ同一視する。
方針：標準の射影と包含を分解式で互いに逆な線形写像にする。
規約：第一成分が始域。使われ方：cone 基底の座標。 -/
def coneDegreeEquiv (k : ℤ) : (mappingCone f).X k ≃ₗ[S] (P.X (k + 1) × Q.X k) where
  toFun x := (((mappingCone.fst f).val.v k (k + 1) rfl).hom x,
    ((mappingCone.snd f).v k k (add_zero k)).hom x)
  invFun x := ((mappingCone.inl f).v (k + 1) k (by omega)).hom x.1 +
    ((mappingCone.inr f).f k).hom x.2
  left_inv x := by
    have h := congrArg (fun a => a.hom x) (mappingCone.id_X f k (k + 1) rfl)
    simpa only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_comp,
      LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] using h
  right_inv x := by
    apply Prod.ext
    · change ((mappingCone.fst f).val.v k (k + 1) rfl).hom
        (((mappingCone.inl f).v (k + 1) k (by omega)).hom x.1 +
          ((mappingCone.inr f).f k).hom x.2) = x.1
      rw [map_add]
      have h₁ := congrArg (fun a => a.hom x.1) (mappingCone.inl_v_fst_v f (k + 1) k rfl)
      have h₂ := congrArg (fun a => a.hom x.2) (mappingCone.inr_f_fst_v f k (k + 1) rfl)
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
        LinearMap.id_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using
        congrArg₂ (· + ·) h₁ h₂ |>.trans (add_zero _)
    · change ((mappingCone.snd f).v k k (add_zero k)).hom
        (((mappingCone.inl f).v (k + 1) k (by omega)).hom x.1 +
          ((mappingCone.inr f).f k).hom x.2) = x.2
      rw [map_add]
      have h₁ := congrArg (fun a => a.hom x.1)
        (mappingCone.inl_v_snd_v f (k + 1) k (by omega))
      have h₂ := congrArg (fun a => a.hom x.2) (mappingCone.inr_f_snd_v f k)
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
        LinearMap.id_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using
        congrArg₂ (· + ·) h₁ h₂ |>.trans (zero_add _)
  map_add' x y := by exact Prod.ext (map_add _ x y) (map_add _ x y)
  map_smul' a x := by exact Prod.ext (map_smul _ a x) (map_smul _ a x)

/-- 概要：cone 座標の第一成分は標準の第一射影。
方針：座標同型の定義を展開する。
規約：始域次数は一つ上。使われ方：微分の第一成分。 -/
theorem coneDegreeEquiv_fst (k : ℤ) (x : (mappingCone f).X k) :
    (coneDegreeEquiv f k x).1 = ((mappingCone.fst f).val.v k (k + 1) rfl).hom x := rfl

/-- 概要：cone 座標の第二成分は標準の第二射影。
方針：座標同型の定義を展開する。
規約：終域次数は変わらない。使われ方：微分の第二成分。 -/
theorem coneDegreeEquiv_snd (k : ℤ) (x : (mappingCone f).X k) :
    (coneDegreeEquiv f k x).2 = ((mappingCone.snd f).v k k (add_zero k)).hom x := rfl

/-- 概要：cone 微分の第一座標は始域の微分の負号である。
方針：標準第一射影と微分の公式を評価する。
規約：コチェイン cone の符号。使われ方：始域側の高さ下降。 -/
theorem coneDegreeEquiv_d_fst (k : ℤ) (x : (mappingCone f).X k) :
    (coneDegreeEquiv f (k + 1) (((mappingCone f).d k (k + 1)).hom x)).1 =
      -((P.d (k + 1) (k + 1 + 1)).hom (coneDegreeEquiv f k x).1) := by
  rw [coneDegreeEquiv_fst, coneDegreeEquiv_fst]
  have h := congrArg (fun a => a.hom x)
    (mappingCone.d_fst_v f k (k + 1) (k + 1 + 1) rfl rfl)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_neg,
    LinearMap.neg_apply, map_neg] using h

/-- 概要：cone 微分の第二座標は射の像と終域の微分の和である。
方針：標準第二射影と微分の公式を評価する。
規約：始域成分の次数で射を評価する。使われ方：像の高さの上限。 -/
theorem coneDegreeEquiv_d_snd (k : ℤ) (x : (mappingCone f).X k) :
    (coneDegreeEquiv f (k + 1) (((mappingCone f).d k (k + 1)).hom x)).2 =
      (f.f (k + 1)).hom (coneDegreeEquiv f k x).1 +
        (Q.d k (k + 1)).hom (coneDegreeEquiv f k x).2 := by
  rw [coneDegreeEquiv_snd, coneDegreeEquiv_fst, coneDegreeEquiv_snd]
  have h := congrArg (fun a => a.hom x) (mappingCone.d_snd_v f k (k + 1) rfl)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_add,
    LinearMap.add_apply] using h

namespace ComplexSemifreeBasis
variable (B : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis S P) (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis S Q)

/-- 概要：cone の直積表示から移した基底。
方針：二つの次数付き基底の直積を座標同型で戻す。
規約：添字は始域側と終域側の和型。使われ方：cone の semibasis。 -/
def coneBasis (k : ℤ) : Module.Basis (B.Index (k + 1) ⊕ C.Index k) S ((mappingCone f).X k) :=
  ((B.basis (k + 1)).prod (C.basis k)).map (coneDegreeEquiv f k).symm

/-- 概要：cone 基底の第一成分の座標公式。
方針：直積基底の表現公式を使う。
規約：和型の左側は始域。使われ方：微分の台の判定。 -/
theorem coneBasis_repr_inl (k : ℤ) (x : (mappingCone f).X k) (i : B.Index (k + 1)) :
    (B.coneBasis f C k).repr x (Sum.inl i) =
      (B.basis (k + 1)).repr (coneDegreeEquiv f k x).1 i := by
  change ((B.basis (k + 1)).prod (C.basis k)).repr (coneDegreeEquiv f k x) (Sum.inl i) = _
  exact Module.Basis.prod_repr_inl _ _ _ _

/-- 概要：cone 基底の第二成分の座標公式。
方針：直積基底の表現公式を使う。
規約：和型の右側は終域。使われ方：微分の台の判定。 -/
theorem coneBasis_repr_inr (k : ℤ) (x : (mappingCone f).X k) (i : C.Index k) :
    (B.coneBasis f C k).repr x (Sum.inr i) =
      (C.basis k).repr (coneDegreeEquiv f k x).2 i := by
  change ((B.basis (k + 1)).prod (C.basis k)).repr (coneDegreeEquiv f k x) (Sum.inr i) = _
  exact Module.Basis.prod_repr_inr _ _ _ _

/-- 概要：cone 基底を直積座標で読むと元の直積基底になる。
方針：基底の移送と座標同型の逆を消去する。
規約：任意の和型添字。使われ方：基底元の微分成分。 -/
theorem coneBasis_coordinates (k : ℤ) (a : B.Index (k + 1) ⊕ C.Index k) :
    coneDegreeEquiv f k (B.coneBasis f C k a) =
      (B.basis (k + 1)).prod (C.basis k) a :=
  (coneDegreeEquiv f k).apply_symm_apply _

/-- 概要：cone 基底の微分の左から左への座標。
方針：始域微分の負号と直積基底の座標を使う。
規約：符号は台に影響しない。使われ方：新しい高さの下降。 -/
theorem coneBasis_d_inl_inl (k : ℤ) (i : B.Index (k + 1))
    (j : B.Index (k + 1 + 1)) :
    (B.coneBasis f C (k + 1)).repr
      (((mappingCone f).d k (k + 1)).hom (B.coneBasis f C k (Sum.inl i))) (Sum.inl j) =
      -((B.basis (k + 1 + 1)).repr
        ((P.d (k + 1) (k + 1 + 1)).hom (B.basis (k + 1) i)) j) := by
  rw [coneBasis_repr_inl, coneDegreeEquiv_d_fst, coneBasis_coordinates,
    Module.Basis.prod_apply_inl_fst, map_neg, Finsupp.neg_apply]

/-- 概要：cone 基底の微分の左から右への座標。
方針：終域の微分の零成分を消し、射の像だけを残す。
規約：射による filtration 保存を要求しない。使われ方：像の高さ制御。 -/
theorem coneBasis_d_inl_inr (k : ℤ) (i : B.Index (k + 1)) (j : C.Index (k + 1)) :
    (B.coneBasis f C (k + 1)).repr
      (((mappingCone f).d k (k + 1)).hom (B.coneBasis f C k (Sum.inl i))) (Sum.inr j) =
      (C.basis (k + 1)).repr ((f.f (k + 1)).hom (B.basis (k + 1) i)) j := by
  rw [coneBasis_repr_inr, coneDegreeEquiv_d_snd, coneBasis_coordinates,
    Module.Basis.prod_apply_inl_fst, Module.Basis.prod_apply_inl_snd, map_zero, add_zero]

/-- 概要：cone 基底の微分の右から左への座標は零。
方針：直積基底の第一成分が零であることを使う。
規約：終域側は部分複体である。使われ方：微分の台の排除。 -/
theorem coneBasis_d_inr_inl (k : ℤ) (i : C.Index k) (j : B.Index (k + 1 + 1)) :
    (B.coneBasis f C (k + 1)).repr
      (((mappingCone f).d k (k + 1)).hom (B.coneBasis f C k (Sum.inr i))) (Sum.inl j) = 0 := by
  rw [coneBasis_repr_inl, coneDegreeEquiv_d_fst, coneBasis_coordinates,
    Module.Basis.prod_apply_inr_fst, map_zero, neg_zero, map_zero, Finsupp.zero_apply]

/-- 概要：cone 基底の微分の右から右への座標。
方針：終域の元の微分の座標へ帰着する。
規約：終域の基底と高さは保持する。使われ方：元の semibasis の下降則。 -/
theorem coneBasis_d_inr_inr (k : ℤ) (i : C.Index k) (j : C.Index (k + 1)) :
    (B.coneBasis f C (k + 1)).repr
      (((mappingCone f).d k (k + 1)).hom (B.coneBasis f C k (Sum.inr i))) (Sum.inr j) =
      (C.basis (k + 1)).repr ((Q.d k (k + 1)).hom (C.basis k i)) j := by
  rw [coneBasis_repr_inr, coneDegreeEquiv_d_snd, coneBasis_coordinates,
    Module.Basis.prod_apply_inr_fst, Module.Basis.prod_apply_inr_snd, map_zero, zero_add]

/-- 概要：semifree な始域と終域の任意の射の cone は semibasis を持つ。
方針：直積基底に始域側の付け直した高さを与え、四つの微分成分を調べる。
規約：射が filtration を保存する仮定なし。使われ方：cone 閉性の構成的証明。 -/
def cone : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis S (mappingCone f) where
  Index k := B.Index (k + 1) ⊕ C.Index k
  basis := B.coneBasis f C
  height k := Sum.elim (B.coneSourceHeight C f (k + 1)) (C.height k)
  lowering k a b hb := by
    have hne := Finsupp.mem_support_iff.mp hb
    cases a with
    | inl i =>
      cases b with
      | inl j =>
        have hj : j ∈ ((B.basis (k + 1 + 1)).repr
            ((P.d (k + 1) (k + 1 + 1)).hom (B.basis (k + 1) i))).support := by
          apply Finsupp.mem_support_iff.mpr
          intro hz
          exact hne ((B.coneBasis_d_inl_inl f C k i j).trans (by rw [hz, neg_zero]))
        exact B.differential_lt_coneSourceHeight C f (k + 1) i j hj
      | inr j =>
        have hj : j ∈ ((C.basis (k + 1)).repr
            ((f.f (k + 1)).hom (B.basis (k + 1) i))).support := by
          apply Finsupp.mem_support_iff.mpr
          exact fun hz => hne ((B.coneBasis_d_inl_inr f C k i j).trans hz)
        exact B.image_lt_coneSourceHeight C f (k + 1) i j hj
    | inr i =>
      cases b with
      | inl j => exact False.elim (hne (B.coneBasis_d_inr_inl f C k i j))
      | inr j =>
        apply C.lowering k i j
        apply Finsupp.mem_support_iff.mpr
        exact fun hz => hne ((B.coneBasis_d_inr_inr f C k i j).trans hz)

end ComplexSemifreeBasis
/-- 概要：semifree 複体間の任意の鎖写像の mapping cone は semifree である。
方針：既存定義との同値で基底を取り出し、cone の semibasis から filtration を構成する。
規約：有界性・有限性・filtration 保存の仮定なし。使われ方：導来圏の cone・cofiber。
-/
theorem complexSemifree_mappingCone (hP : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S P) (hQ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S Q) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S (mappingCone f) := by
  obtain ⟨B⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_nonempty_basis hP
  obtain ⟨C⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_nonempty_basis hQ
  exact (B.cone f C).complexSemifree

end SerrePositivity.InfinityCategories.Project.DerivedCategories
