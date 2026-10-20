module
public import SerrePositivity.InfinityCategories.Derived.DGLastHornConePrimitive
public import SerrePositivity.InfinityCategories.DGNerve.HomTransport

/-! # 命題的に隣接する次数での cone 原始元座標

概要：q+1=r を明示入力にして、cone の二座標と微分を固定した次数で読む。
方針：次数の等式を消去し、既存の標準座標補題へ帰着する。
規約：型輸送の証明は保持する。使われ方：一般最後外ホーンの Q・A の回収。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve CochainComplex HomComplex
variable {A : Type u} [CommRing A]

/-- 第一座標の負の微分を、指定した次の次数 r で読む。 -/
lemma dgComplexConePrimitive_fst_at {M N : Complex A} (f : M ⟶ N)
    (q r : ℤ) (hqr : q + 1 = r) (h : (mappingCone f).X q) (z : (mappingCone f).X r)
    (dh : (mappingCone f).d q r h = z) :
    M.d r (r + 1) (-(mappingCone.fst f).val.v q r hqr h) =
      (mappingCone.fst f).val.v r (r + 1) rfl z := by
  subst r
  exact dgComplexConePrimitive_fst f q h z dh

/-- 第二座標の微分を、指定した次の次数 r と同じ Q 座標で読む。 -/
lemma dgComplexConePrimitive_snd_at {M N : Complex A} (f : M ⟶ N)
    (q r : ℤ) (hqr : q + 1 = r) (h : (mappingCone f).X q) (z : (mappingCone f).X r)
    (dh : (mappingCone f).d q r h = z) :
    N.d q r ((mappingCone.snd f).v q q (add_zero q) h) =
      (mappingCone.snd f).v r r (add_zero r) z +
        f.f r (-(mappingCone.fst f).val.v q r hqr h) := by
  subst r
  exact dgComplexConePrimitive_snd f q h z dh

/-- 命題的に次の次数 r への Hom 微分は、標準微分の線形輸送そのもの。 -/
lemma dgGradedHomTransport_differential_to {D : Type v} [DGCategory A D]
    {x y : D} (q r : ℤ) (hqr : q + 1 = r) (f : GradedHom A x y q) :
    gradedHomTransport rfl rfl hqr (differential A f) = (homObject A D x y).d q r f := by
  subst r
  rfl

/-- 指定した隣接次数の二座標から cone 成分を作る。 -/
def dgComplexConeElementMkAt {M N : Complex A} (f : M ⟶ N)
    (q r : ℤ) (hqr : q + 1 = r) (u : M.X r) (v : N.X q) : (mappingCone f).X q := by
  subst r
  exact complexConeElementMk A f q u v

/-- 隣接次数を明示した cone 成分の第一座標。 -/
lemma dgComplexConeElementMkAt_fst {M N : Complex A} (f : M ⟶ N)
    (q r : ℤ) (hqr : q + 1 = r) (u : M.X r) (v : N.X q) :
    (mappingCone.fst f).val.v q r hqr (dgComplexConeElementMkAt f q r hqr u v) = u := by
  subst r
  exact complexConeElementMk_fst A f q u v

/-- 隣接次数を明示した cone 成分の第二座標。 -/
lemma dgComplexConeElementMkAt_snd {M N : Complex A} (f : M ⟶ N)
    (q r : ℤ) (hqr : q + 1 = r) (u : M.X r) (v : N.X q) :
    (mappingCone.snd f).v q q (add_zero q) (dgComplexConeElementMkAt f q r hqr u v) = v := by
  subst r
  exact complexConeElementMk_snd A f q u v

/-- 二つの指定次数の微分式から、同じ二残差への cone 微分を得る。 -/
lemma dgComplexConeElementMkAt_differential {M N : Complex A} (f : M ⟶ N)
    (q r : ℤ) (hqr : q + 1 = r) (u : M.X r) (v : N.X q) (a : M.X (r + 1)) (b : N.X r)
    (du : M.d r (r + 1) u = a) (dv : N.d q r v = b + f.f r u) :
    (mappingCone f).d q r (dgComplexConeElementMkAt f q r hqr (-u) v) =
      complexConeElementMk A f r a b := by
  subst r
  exact dgComplexConeElementMk_differential f q u v a b du dv

end SerrePositivity.InfinityCategories
