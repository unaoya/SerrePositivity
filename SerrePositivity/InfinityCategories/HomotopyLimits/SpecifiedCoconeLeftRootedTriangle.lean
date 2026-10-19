module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeLeftTransportEdge
public import SerrePositivity.InfinityCategories.HomotopyLimits.RelativePrefixTriangle
public import SerrePositivity.InfinityCategories.HomotopyLimits.RootedHomRootCoordinates

/-!
概要：元の付加比較辺と標準の左輸送辺を、native な左二単体を覆う実際の三角形へ束ねる。
方針：指定した二辺を内ホーン上に貼り、同じ底の二単体上で持ち上げる。
規約：標準 prism の辺、付加辺、底の二単体を全て厳密に保持する。
使われ方：左 HL の Hom 比較を元の左三角形の全 Hom 族へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p))
local notation "q" => sliceUnderProjection (f ≫ (i ≫ p))
local notation "r" => sliceUnderRestrict (i ≫ p) f
local notation "a" => colimitAttachmentRestrictionEdge c hc f (i ≫ p) rfl dB
local notation "k" => specifiedCoconeLeftTransportEdge hp p c hc dB dC
local notation "σ" => partialColimitSpanLeftTriangle c hc f (i ≫ p) rfl dB
  g (j ≫ p) (coconePushoutBoundary_eq hp p) dC

/-- 元の二辺と native な二単体の全単体表示を同時に保つ、実際の左三角形。 -/
structure SpecifiedCoconeLeftTriangleData where
  simplex : (Δ[2] : SSet.{u + 1}) ⟶ sliceUnder (f ≫ (i ≫ p))
  first : stdSimplex.δ (2 : Fin 3) ≫ simplex = SSet.yonedaEquiv.symm (a).edge
  second : stdSimplex.δ (0 : Fin 3) ≫ simplex = SSet.yonedaEquiv.symm (k).edge ≫ r
  projection : simplex ≫ q = SSet.yonedaEquiv.symm (σ).simplex

/-- 標準 prism 自身の左辺と元の付加辺を持つ、同じ底の左三角形を構成する。 -/
def specifiedCoconeLeftTriangleData : SpecifiedCoconeLeftTriangleData hp p c hc dB dC :=
  Classical.choice (by
    have ha : stdSimplex.δ (0 : Fin 2) ≫ SSet.yonedaEquiv.symm (a).edge =
        stdSimplex.δ (1 : Fin 2) ≫ (SSet.yonedaEquiv.symm (k).edge ≫ r) := by
      have hn : SSet.yonedaEquiv.symm
          ((normalizedCoconeRestriction (i ≫ p) f rfl).app (Opposite.op ⦋0⦌) dB) =
            SSet.yonedaEquiv.symm dB ≫ r := by
        simpa only [normalizedCoconeRestriction, eqToHom_refl, Category.comp_id] using
          (SSet.yonedaEquiv_symm_comp dB r).symm
      have hk := congrArg (fun z ↦ z ≫ r) (k).δ_one_yonedaEquiv_symm
      exact (a).δ_zero_yonedaEquiv_symm.trans
        (hn.trans (hk.symm.trans (Category.assoc _ _ _)))
    have he : stdSimplex.δ (2 : Fin 3) ≫ SSet.yonedaEquiv.symm (σ).simplex =
        SSet.yonedaEquiv.symm (a).edge ≫ q := by
      rw [stdSimplex.δ_comp_yonedaEquiv_symm, (σ).d₂, SSet.Edge.ofTruncated_edge]
      exact (colimitAttachmentRestrictionEdge_projection_map c hc f (i ≫ p) rfl dB).symm
    have ht : stdSimplex.δ (0 : Fin 3) ≫ SSet.yonedaEquiv.symm (σ).simplex =
        (SSet.yonedaEquiv.symm (k).edge ≫ r) ≫ q := by
      rw [stdSimplex.δ_comp_yonedaEquiv_symm, (σ).d₀, Category.assoc,
        sliceUnderRestrict_projection, SSet.yonedaEquiv_symm_comp,
        specifiedCoconeLeftTransportEdge_projection]
    obtain ⟨s, hs₀, hs₁, hq⟩ := exists_prefixTriangle_over_innerFibration q
      (SSet.yonedaEquiv.symm (a).edge) (SSet.yonedaEquiv.symm (k).edge ≫ r) ha
      (SSet.yonedaEquiv.symm (σ).simplex) he ht
    exact ⟨⟨s, hs₀, hs₁, hq⟩⟩)

/-- 実際の左二辺を面として保持する、同じ左三角形の図式。 -/
def specifiedCoconeLeftRootedTriangle :
    (Δ[2] : SSet.{u + 1}) ⟶ sliceUnder (f ≫ (i ≫ p)) :=
  (specifiedCoconeLeftTriangleData hp p c hc dB dC).simplex

/-- 第一辺は、元の実際の付加比較辺そのもの。 -/
lemma specifiedCoconeLeftRootedTriangle_first :
    stdSimplex.δ (2 : Fin 3) ≫ specifiedCoconeLeftRootedTriangle hp p c hc dB dC =
      SSet.yonedaEquiv.symm (a).edge :=
  (specifiedCoconeLeftTriangleData hp p c hc dB dC).first

/-- 終端辺は、標準 prism 自身の左輸送辺を共通部分へ制限したもの。 -/
lemma specifiedCoconeLeftRootedTriangle_second :
    stdSimplex.δ (0 : Fin 3) ≫ specifiedCoconeLeftRootedTriangle hp p c hc dB dC =
      SSet.yonedaEquiv.symm (k).edge ≫ r :=
  (specifiedCoconeLeftTriangleData hp p c hc dB dC).second

/-- 底は、元の native な左二単体そのもの。 -/
lemma specifiedCoconeLeftRootedTriangle_projection :
    specifiedCoconeLeftRootedTriangle hp p c hc dB dC ≫ q =
      SSet.yonedaEquiv.symm (σ).simplex :=
  (specifiedCoconeLeftTriangleData hp p c hc dB dC).projection

/-- 左三角形の最初の頂点は、元の共通部分の始対象。 -/
lemma specifiedCoconeLeftRootedTriangle_initial :
    (stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3)) ≫
        specifiedCoconeLeftRootedTriangle hp p c hc dB dC = SSet.yonedaEquiv.symm c := by
  rw [Category.assoc, specifiedCoconeLeftRootedTriangle_first, (a).δ_one_yonedaEquiv_symm]

/-- 同じ左三角形の長辺の底は、元の native な共通脚そのもの。 -/
lemma specifiedCoconeLeftRootedTriangle_rootProjection :
    (stdSimplex.δ (1 : Fin 3) ≫ specifiedCoconeLeftRootedTriangle hp p c hc dB dC) ≫ q =
      specifiedCoconeNativeRootEdge hp p c hc dB dC := by
  rw [Category.assoc, specifiedCoconeLeftRootedTriangle_projection,
    stdSimplex.δ_comp_yonedaEquiv_symm, (σ).d₁]
  rfl

end
end SerrePositivity.InfinityCategories.HomotopyLimits
