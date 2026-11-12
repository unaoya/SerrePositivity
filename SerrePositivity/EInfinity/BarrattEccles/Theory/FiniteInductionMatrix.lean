module

public import Mathlib.RepresentationTheory.FiniteIndex
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import SerrePositivity.EInfinity.BarrattEccles.Theory.RepresentationComplex

/-!
# 有限指数の誘導表示の行列比較

## 概要
HA 3.2.4.7 の入力の分解に使う、指定包含と射影から作る誘導・余誘導比較。

## 方針
部分群の外の行列成分の消滅と、包含・射影の合成から、標準の誘導・余誘導同型と照合する。

## 規約
群の位数の可逆性を仮定しない。包含と射影は指定された同変射を使う。

## 使われ方
二色の標準パターンの軌道から誘導した入力表現の同定。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory
attribute [local instance] Classical.propDecidable
variable {R G : Type u} [CommRing R] [Group G] (H : Subgroup G)
  (V : Rep.{u} R H) (W : Rep.{u} R G)

/-- 指定包含を誘導表現からの射へ延ばす。 -/
abbrev finiteInductionInclusion (ι : V ⟶ Rep.res H.subtype W) : Rep.ind H.subtype V ⟶ W :=
  (Rep.indResHomEquiv H.subtype V W).symm ι

/-- 指定射影を余誘導表現への射へ延ばす。 -/
abbrev finiteCoinductionProjection (π : Rep.res H.subtype W ⟶ V) :
    W ⟶ Rep.coind H.subtype V := Rep.resCoindToHom H.subtype W V π

/-- 誘導した包含の、指定生成元における値。 -/
lemma finiteInductionInclusion_mk (ι : V ⟶ Rep.res H.subtype W) (g : G) (x : V) :
    (finiteInductionInclusion H V W ι).hom (Representation.IndV.mk H.subtype V.ρ g x) =
      W.ρ g⁻¹ (ι.hom x) := by
  simp [finiteInductionInclusion, Rep.indResHomEquiv]

/-- 余誘導への射影の、群の元での評価。 -/
lemma finiteCoinductionProjection_apply (π : Rep.res H.subtype W ⟶ V) (w : W) (g : G) :
    ((finiteCoinductionProjection H V W π).hom w).1 g = π.hom (W.ρ g w) := rfl

/-- 部分群以外の行列成分が零なら、包含から射影への比較は標準の誘導・余誘導比較。 -/
lemma finiteInduction_projection_matrix [H.FiniteIndex]
    (ι : V ⟶ Rep.res H.subtype W) (π : Rep.res H.subtype W ⟶ V)
    (hιπ : ι ≫ π = 𝟙 V)
    (hoff : ∀ (g : G), g ∉ H → ∀ x : V, π.hom (W.ρ g (ι.hom x)) = 0) :
    finiteInductionInclusion H V W ι ≫ finiteCoinductionProjection H V W π =
      (Rep.indCoindIso V).hom := by
  classical
  have hιπx (x : V) : π.hom (ι.hom x) = x := by
    exact congrArg (fun f : V ⟶ V => f.hom x) hιπ
  have hind (g : G) (x : V) (t : G) :
      ((Rep.indCoindIso V).hom.hom (Representation.IndV.mk H.subtype V.ρ g x)).1 t =
        Rep.indToCoindAux V g x t := by
    simp [Rep.indCoindIso, Rep.indToCoind, Representation.IndV.mk]
  ext g x t
  change ((finiteCoinductionProjection H V W π).hom
    ((finiteInductionInclusion H V W ι).hom
      (Representation.IndV.mk H.subtype V.ρ g x))).1 t =
      ((Rep.indCoindIso V).hom.hom (Representation.IndV.mk H.subtype V.ρ g x)).1 t
  rw [finiteInductionInclusion_mk, finiteCoinductionProjection_apply, hind]
  by_cases ht : (QuotientGroup.rightRel H).r t g
  · rcases ht with ⟨s, rfl⟩
    change π.hom (W.ρ ((s : G) * g) (W.ρ g⁻¹ (ι.hom x))) =
      Rep.indToCoindAux V g x ((s : G) * g)
    rw [Rep.indToCoindAux_mul_snd, Rep.indToCoindAux_self,
      ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_right]
    have hc := Rep.hom_comm_apply ι s x
    change ι.hom (V.ρ s x) = W.ρ (s : G) (ι.hom x) at hc
    rw [← hc, hιπx]
  · rw [Rep.indToCoindAux_of_not_rel _ _ _ ht,
      ← Module.End.mul_apply, ← map_mul]
    apply hoff
    intro hm
    apply ht
    exact ⟨⟨t * g⁻¹, hm⟩, by simp⟩


/-- 異なる色成分の行列が全て零なら、誘導包含から余誘導射影への射も零。 -/
lemma finiteInduction_cross_matrix (H' : Subgroup G) (V' : Rep.{u} R H')
    (ι : V ⟶ Rep.res H.subtype W) (π : Rep.res H'.subtype W ⟶ V')
    (hoff : ∀ (g : G) (x : V), π.hom (W.ρ g (ι.hom x)) = 0) :
    finiteInductionInclusion H V W ι ≫ finiteCoinductionProjection H' V' W π = 0 := by
  ext g x t
  change ((finiteCoinductionProjection H' V' W π).hom
    ((finiteInductionInclusion H V W ι).hom
      (Representation.IndV.mk H.subtype V.ρ g x))).1 t = 0
  rw [finiteInductionInclusion_mk, finiteCoinductionProjection_apply,
    ← Module.End.mul_apply, ← map_mul]
  exact hoff _ _

open CategoryTheory.Limits

/-- 指定された誘導包含・射影と行列の直交性から作る双錐。 -/
def finiteInductionBicone {J : Type u} [Fintype J]
    (Hs : J → Subgroup G) [∀ j, (Hs j).FiniteIndex]
    (Vs : ∀ j, Rep.{u} R (Hs j))
    (ι : ∀ j, Vs j ⟶ Rep.res (Hs j).subtype W)
    (π : ∀ j, Rep.res (Hs j).subtype W ⟶ Vs j)
    (hdiag : ∀ j, ι j ≫ π j = 𝟙 (Vs j))
    (hself : ∀ j (g : G), g ∉ Hs j → ∀ x : Vs j, (π j).hom (W.ρ g ((ι j).hom x)) = 0)
    (hcross : ∀ j k, j ≠ k → ∀ (g : G) (x : Vs j),
      (π k).hom (W.ρ g ((ι j).hom x)) = 0) :
    Bicone (fun j => Rep.ind (Hs j).subtype (Vs j)) where
  pt := W
  ι j := finiteInductionInclusion (Hs j) (Vs j) W (ι j)
  π j := finiteCoinductionProjection (Hs j) (Vs j) W (π j) ≫ (Rep.indCoindIso (Vs j)).inv
  ι_π := by
    classical
    intro j k
    by_cases h : j = k
    · subst k
      rw [← Category.assoc,
        finiteInduction_projection_matrix (Hs j) (Vs j) W (ι j) (π j) (hdiag j) (hself j)]
      simp
    · rw [← Category.assoc,
        finiteInduction_cross_matrix (Hs j) (Vs j) W (Hs k) (Vs k) (ι j) (π k)
          (hcross j k h), zero_comp]
      simp [h]

/-- 誘導した指定包含が射を検出すれば、直交する誘導表示は実際の有限直和となる。 -/
def finiteInductionBiconeIsBilimit {J : Type u} [Fintype J]
    (Hs : J → Subgroup G) [∀ j, (Hs j).FiniteIndex]
    (Vs : ∀ j, Rep.{u} R (Hs j))
    (ι : ∀ j, Vs j ⟶ Rep.res (Hs j).subtype W)
    (π : ∀ j, Rep.res (Hs j).subtype W ⟶ Vs j)
    (hdiag : ∀ j, ι j ≫ π j = 𝟙 (Vs j))
    (hself : ∀ j (g : G), g ∉ Hs j → ∀ x : Vs j, (π j).hom (W.ρ g ((ι j).hom x)) = 0)
    (hcross : ∀ j k, j ≠ k → ∀ (g : G) (x : Vs j),
      (π k).hom (W.ρ g ((ι j).hom x)) = 0)
    (hcover : ∀ {Z : Rep.{u} R G} (f g : W ⟶ Z),
      (∀ j, finiteInductionInclusion (Hs j) (Vs j) W (ι j) ≫ f =
        finiteInductionInclusion (Hs j) (Vs j) W (ι j) ≫ g) → f = g) :
    (finiteInductionBicone W Hs Vs ι π hdiag hself hcross).IsBilimit := by
  let b := finiteInductionBicone W Hs Vs ι π hdiag hself hcross
  apply isBilimitOfTotal b
  apply hcover
  intro j
  change b.ι j ≫ (∑ k, b.π k ≫ b.ι k) = b.ι j ≫ 𝟙 W
  classical
  rw [Preadditive.comp_sum, Finset.sum_eq_single j]
  · rw [← Category.assoc, bicone_ι_π_self, Category.id_comp]
    exact (Category.comp_id _).symm
  · intro k _ hkj
    rw [← Category.assoc, bicone_ι_π_ne b hkj.symm, zero_comp]
  · simp

/-- 指定包含を、微分を保つ誘導表現の複体からの射へ延ばす。 -/
def finiteInductionCochainInclusion
    (K : CochainComplex (Rep.{u} R H) ℤ) (L : CochainComplex (Rep.{u} R G) ℤ)
    (ι : K ⟶ ((Rep.resFunctor H.subtype).mapHomologicalComplex (.up ℤ)).obj L) :
    ((Rep.indFunctor R H.subtype).mapHomologicalComplex (.up ℤ)).obj K ⟶ L where
  f i := finiteInductionInclusion H (K.X i) (L.X i) (ι.f i)
  comm' i j _ := by
    apply (Rep.indResHomEquiv H.subtype (K.X i) (L.X j)).injective
    ext x
    have hc := congrArg (fun f => f.hom x) (ι.comm i j)
    simpa [Rep.indResHomEquiv, Rep.indMap, finiteInductionInclusion] using hc

/-- 指定射影を、微分を保つ余誘導表現の複体への射へ延ばす。 -/
def finiteCoinductionCochainProjection
    (K : CochainComplex (Rep.{u} R H) ℤ) (L : CochainComplex (Rep.{u} R G) ℤ)
    (π : ((Rep.resFunctor H.subtype).mapHomologicalComplex (.up ℤ)).obj L ⟶ K) :
    L ⟶ ((Rep.coindFunctor R H.subtype).mapHomologicalComplex (.up ℤ)).obj K where
  f i := finiteCoinductionProjection H (K.X i) (L.X i) (π.f i)
  comm' i j _ := by
    symm
    let adj := Rep.resCoindAdjunction R H.subtype
    change L.d i j ≫ (adj.homEquiv _ _) (π.f j) =
      (adj.homEquiv _ _) (π.f i) ≫ (Rep.coindFunctor R H.subtype).map (K.d i j)
    rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right]
    exact congrArg (adj.homEquiv _ _) (π.comm i j).symm

end SerrePositivity.EInfinity
