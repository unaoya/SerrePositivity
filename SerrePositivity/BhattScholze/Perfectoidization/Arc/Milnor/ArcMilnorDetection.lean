module

public import SerrePositivity.BhattScholze.Perfectoidization.Arc.Milnor.ArcMilnorTensor
public import SerrePositivity.HomologicalAlgebra.Cech.BaseChange
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
## 概要
Milnor 四角形での余鎖複体の完全性の検出。
## 方針
次数ごとの短完全列を複体の短完全列にしてホモロジー長完全列を使う。
## 規約
係数加群を左からテンソルする。二つの中間係数は加群の直積を取る。
## 使われ方
BM18 Proposition 4.8 の証明 (5) の構造層での完全性。
-/

@[expose] public noncomputable section

universe u

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.HomologicalComplex

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

set_option backward.isDefEq.respectTransparency false

variable {V : Type u} [CommRing V]

/-- 係数加群を左からテンソルして得る余鎖複体。 -/
def _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.tensorCochain (K : CochainComplex (ModuleCat.{u} V) ℕ) (W : ModuleCat.{u} V) :
    CochainComplex (ModuleCat.{u} V) ℕ :=
  ((tensorLeft W).mapHomologicalComplex (.up ℕ)).obj K

/-- 係数のテンソルを余鎖複体に施す関手。 -/
def _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.tensorCochainFunctor (K : CochainComplex (ModuleCat.{u} V) ℕ) :
    ModuleCat.{u} V ⥤ CochainComplex (ModuleCat.{u} V) ℕ where
  obj := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.tensorCochain K
  map f := (NatTrans.mapHomologicalComplex ((tensoringLeft _).map f) (.up ℕ)).app K
  map_id W := by
    ext n : 1
    exact (tensorRight (K.X n)).map_id W
  map_comp f g := by
    ext n : 1
    exact (tensorRight (K.X n)).map_comp f g

instance (K : CochainComplex (ModuleCat.{u} V) ℕ) : (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.tensorCochainFunctor K).Additive where
  map_add := by
    intro W Z f g
    ext n : 1
    change (tensorRight (K.X n)).map (f + g) =
      (tensorRight (K.X n)).map f + (tensorRight (K.X n)).map g
    exact Functor.map_add _

theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.tensorCochain_prod_acyclic (K : CochainComplex (ModuleCat.{u} V) ℕ)
    (L Q : Type u) [AddCommGroup L] [Module V L] [AddCommGroup Q] [Module V Q]
    (hl : (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.tensorCochain K (ModuleCat.of V L)).Acyclic)
    (hq : (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.tensorCochain K (ModuleCat.of V Q)).Acyclic) :
    (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.tensorCochain K (ModuleCat.of V (L × Q))).Acyclic := by
  intro n
  rw [exactAt_iff_isZero_homology, IsZero.iff_id_eq_zero]
  let F := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.tensorCochainFunctor K ⋙ homologyFunctor (ModuleCat V) (.up ℕ) n
  let π₁ : ModuleCat.of V (L × Q) ⟶ ModuleCat.of V L := ModuleCat.ofHom (LinearMap.fst V L Q)
  let π₂ : ModuleCat.of V (L × Q) ⟶ ModuleCat.of V Q := ModuleCat.ofHom (LinearMap.snd V L Q)
  let ι₁ : ModuleCat.of V L ⟶ ModuleCat.of V (L × Q) := ModuleCat.ofHom (LinearMap.inl V L Q)
  let ι₂ : ModuleCat.of V Q ⟶ ModuleCat.of V (L × Q) := ModuleCat.ofHom (LinearMap.inr V L Q)
  have he : π₁ ≫ ι₁ + π₂ ≫ ι₂ = 𝟙 _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨x,y⟩
    change (x, 0) + (0, y) = (x, y)
    simp
  have z₁ : IsZero (F.obj (ModuleCat.of V L)) := (exactAt_iff_isZero_homology _ _).mp (hl n)
  have z₂ : IsZero (F.obj (ModuleCat.of V Q)) := (exactAt_iff_isZero_homology _ _).mp (hq n)
  change 𝟙 (F.obj (ModuleCat.of V (L × Q))) = 0
  rw [← F.map_id, ← he, Functor.map_add, Functor.map_comp, Functor.map_comp,
    z₁.eq_zero_of_tgt (F.map π₁), z₂.eq_zero_of_tgt (F.map π₂), zero_comp, zero_comp, add_zero]

/-- 次数ごとの Tor₁ 消滅により、係数短完全列は複体の短完全列を誘導する。 -/
theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.tensorCochain_shortExact (K : CochainComplex (ModuleCat.{u} V) ℕ)
    (T : ShortComplex (ModuleCat.{u} V)) (hT : T.ShortExact)
    (htor : ∀ n, Subsingleton (_root_.SerrePositivity.TorModule V 1 (K.X n) T.X₃)) :
    (T.map (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.tensorCochainFunctor K)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let e := BraidedCategory.tensorLeftIsoTensorRight (K.X n)
  have h := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.shortExact_tensorLeft_of_tor (K.X n) T hT (htor n)
  exact ShortComplex.shortExact_of_iso (ShortComplex.mapNatIso T e) h

/-- 係数列の中央と右端での完全性から左端での完全性を得る。 -/
theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.acyclic_of_tensorShortExact (K : CochainComplex (ModuleCat.{u} V) ℕ)
    (T : ShortComplex (ModuleCat.{u} V)) (hT : T.ShortExact)
    (htor : ∀ n, Subsingleton (_root_.SerrePositivity.TorModule V 1 (K.X n) T.X₃))
    (h₂ : (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.tensorCochain K T.X₂).Acyclic) (h₃ : (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.tensorCochain K T.X₃).Acyclic) :
    (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.tensorCochain K T.X₁).Acyclic := by
  let S := T.map (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.tensorCochainFunctor K)
  have hqIso : QuasiIso S.g := by
    rw [quasiIso_iff]
    intro n
    exact (quasiIsoAt_iff_exactAt S.g n (h₂ n)).mpr (h₃ n)
  exact (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.tensorCochain_shortExact K T hT htor).acyclic_X₁ hqIso

/-- 基底環を係数とするテンソルは元の余鎖複体に同型。 -/
def _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.tensorCochain_unitIso (K : CochainComplex (ModuleCat.{u} V) ℕ) :
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.tensorCochain K (ModuleCat.of V V) ≅ K :=
  (NatIso.mapHomologicalComplex (leftUnitorNatIso (ModuleCat.{u} V)) (.up ℕ)).app K ≪≫
    (Functor.mapHomologicalComplexIdIso (ModuleCat.{u} V) (.up ℕ)).app K

/-- 次数ごとの Tor₁ 消滅と Milnor 四角形の三つの角での完全性から元の完全性を得る。
（BM18 Lemma 4.4 と Proposition 4.8 の証明の、構造層の場合。） -/
theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.acyclic_of_milnorTensor [IsDomain V] [ValuationRing V] (P : Ideal V) [P.IsPrime]
    (K : CochainComplex (ModuleCat.{u} V) ℕ)
    (htor : ∀ n, Subsingleton (_root_.SerrePositivity.TorModule V 1 (K.X n) P.ResidueField))
    (hl : (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.tensorCochain K (ModuleCat.of V (Localization.AtPrime P))).Acyclic)
    (hq : (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.tensorCochain K (ModuleCat.of V (V ⧸ P))).Acyclic)
    (hr : (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.tensorCochain K (ModuleCat.of V P.ResidueField)).Acyclic) :
    K.Acyclic := by
  have h₁ := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.acyclic_of_tensorShortExact K (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.milnorModuleComplex P)
    (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.milnorModuleComplex_shortExact P) htor (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.tensorCochain_prod_acyclic K _ _ hl hq) hr
  exact fun n => (h₁ n).of_iso (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.tensorCochain_unitIso K)

end SerrePositivity.BhattScholze.Perfectoidization.Derived
