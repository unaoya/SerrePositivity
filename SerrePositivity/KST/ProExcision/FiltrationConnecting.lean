module

public import SerrePositivity.KST.ProExcision.ConeConnecting

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# 濾過スペクトル対象の連結写像

概要：実際の濾過から作ったスペクトル対象の δ を複体の cone の境界へ比較する。
方針：濾過への引き戻しの標準同型とホモトピー圏のホモロジー比較を追う。
規約：元の濾過の射を変えず、比較同型を明示する。
使われ方：KST Lemma 4.10 の補助初頁微分の計算。
-/

universe u v w

namespace SerrePositivity.KST.ProExcision

open CategoryTheory CategoryTheory.Limits HomologicalComplex

variable {R : Type u} [CommRing R]

/-- 概要：濾過へ引き戻した cone スペクトル対象の第三射は、元の複体の合成 cone 三角形の第三射。
方針：引き戻しに入る標準同型を展開し、恒等射の cone 写像を簡約する。
規約：ホモトピー圏への商関手のシフト比較を含む。
使われ方：KST Lemma 4.10 のスペクトル対象の δ の追跡。 -/
theorem filtrationTriangulated_delta {I : Type v} [Category.{w} I]
    (F : I ⥤ CochainComplex (ModuleCat.{u} R) ℤ)
    {i j k : I} (f : i ⟶ j) (g : j ⟶ k) :
    ((HomotopyCategory.spectralObjectMappingCone (ModuleCat.{u} R)).precomp F).δ f g =
      ShiftedHom.map (CochainComplex.mappingConeCompTriangle (F.map f) (F.map g)).mor₃
        (HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)) := by
  simp [Triangulated.SpectralObject.δ, Triangulated.SpectralObject.precomp,
    HomotopyCategory.spectralObjectMappingCone, HomotopyCategory.composableArrowsFunctor,
    Functor.mapComposableArrowsObjMk₁Iso, ComposableArrows.isoMk₁, ShiftedHom.map, CochainComplex.mappingCone.map_id]

/-- 概要：濾過スペクトル対象の δ は、合成 cone 三角形のシフトつきホモロジー写像。
方針：ホモトピー圏の第三射を具体化し、ホモロジー比較同型の自然性を使う。
規約：左右の区間ホモロジー比較を明示する。使われ方：KST Lemma 4.10 の初頁微分。 -/
theorem filtrationInterval_delta {I : Type v} [Category.{w} I]
    (F : I ⥤ CochainComplex (ModuleCat.{u} R) ℤ)
    {i j k : I} (f : i ⟶ j) (g : j ⟶ k) (n : ℤ) :
    (filteredHomologySpectralObject F).δ f g n (n + 1) rfl ≫
      (filtrationIntervalHomologyIso F f (n + 1)).hom =
      (filtrationIntervalHomologyIso F g n).hom ≫
        (homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0).shiftMap
          (CochainComplex.mappingConeCompTriangle (F.map f) (F.map g)).mor₃
          n (n + 1) (by omega) := by
  change (HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0).shiftMap
    (((HomotopyCategory.spectralObjectMappingCone (ModuleCat.{u} R)).precomp F).δ f g)
    n (n + 1) (by omega) ≫ _ = _
  rw [filtrationTriangulated_delta, HomotopyCategory.homologyFunctor_shiftMap]
  simp only [filtrationIntervalHomologyIso, Iso.app_hom, Category.assoc]
  erw [Iso.inv_hom_id_app]
  rfl

/-- 概要：濾過の δ を実際の商への比較で移すと、短完全列の δ と左の商射の合成になる。
方針：区間ホモロジーを cone に移し、合成 cone 三角形の商比較を適用する。
規約：右の商について短完全性を明示する。
使われ方：KST Lemma 4.10 の隣接項の微分比較。 -/
theorem filtrationInterval_delta_quotient {I : Type v} [Category.{w} I]
    (F : I ⥤ CochainComplex (ModuleCat.{u} R) ℤ)
    {i j k : I} (f : i ⟶ j) (g : j ⟶ k)
    {Q₀ Q₁ : CochainComplex (ModuleCat.{u} R) ℤ}
    (p : F.obj j ⟶ Q₀) (q : F.obj k ⟶ Q₁)
    (hf : F.map f ≫ p = 0) (hg : F.map g ≫ q = 0)
    (hT : (ShortComplex.mk (F.map g) q hg).ShortExact) (n : ℤ) :
    (filteredHomologySpectralObject F).δ f g n (n + 1) rfl ≫
      (filtrationIntervalHomologyIso F f (n + 1)).hom ≫
        homologyMap (CochainComplex.mappingCone.descShortComplex
          (ShortComplex.mk (F.map f) p hf)) (n + 1) =
      (filtrationIntervalHomologyIso F g n).hom ≫
        homologyMap (CochainComplex.mappingCone.descShortComplex
          (ShortComplex.mk (F.map g) q hg)) n ≫
          hT.δ n (n + 1) rfl ≫ homologyMap p (n + 1) := by
  rw [← Category.assoc, filtrationInterval_delta, Category.assoc,
    coneCompositeConnecting_quotient (F.map f) (F.map g) p q hf hg hT n]

/-- 概要：濾過の δ を、次数ごとの分裂から作った境界のホモロジー写像で表す。
方針：商への比較に続いて短完全列の δ と分裂境界の一致を適用する。
規約：分裂を複体の射とは仮定しない。使われ方：KST Lemma 4.10 の初頁微分の計算。 -/
theorem filtrationInterval_delta_split {I : Type v} [Category.{w} I]
    (F : I ⥤ CochainComplex (ModuleCat.{u} R) ℤ)
    {i j k : I} (f : i ⟶ j) (g : j ⟶ k)
    {Q₀ Q₁ : CochainComplex (ModuleCat.{u} R) ℤ}
    (p : F.obj j ⟶ Q₀) (q : F.obj k ⟶ Q₁)
    (hf : F.map f ≫ p = 0) (hg : F.map g ≫ q = 0)
    (hT : (ShortComplex.mk (F.map g) q hg).ShortExact)
    (σ : ∀ a, ((ShortComplex.mk (F.map g) q hg).map (eval _ _ a)).Splitting) (n : ℤ) :
    (filteredHomologySpectralObject F).δ f g n (n + 1) rfl ≫
      (filtrationIntervalHomologyIso F f (n + 1)).hom ≫
        homologyMap (CochainComplex.mappingCone.descShortComplex
          (ShortComplex.mk (F.map f) p hf)) (n + 1) =
      (filtrationIntervalHomologyIso F g n).hom ≫
        homologyMap (CochainComplex.mappingCone.descShortComplex
          (ShortComplex.mk (F.map g) q hg)) n ≫
          (homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0).shiftMap
            (CochainComplex.homOfDegreewiseSplit (ShortComplex.mk (F.map g) q hg) σ)
            n (n + 1) (by omega) ≫ homologyMap p (n + 1) := by
  rw [filtrationInterval_delta_quotient F f g p q hf hg hT n,
    splitBoundary_connecting_eq_shiftMap (ShortComplex.mk (F.map g) q hg) σ hT n]

end SerrePositivity.KST.ProExcision
