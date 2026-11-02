module

public import SerrePositivity.InfinityCategories.Core.CoconeTransportPrism
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.MappingCylinderOverMono

/-!
概要：定値図式への指定自然変換から、同じ図式と指定頂点を持つ native な全余錐を得る。
方針：終端の定値全余錐を、頂点固定の prism で元の自然変換に沿って戻す。
規約：元の図式・自然変換・頂点を保持。余極限性は主張しない。
使われ方：元の F を頂点とする小さい Yoneda 密度余錐の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の自然変換と同じ余錐を結ぶ、頂点固定の全円柱の実現データ。 -/
structure HomotopyConstCoconeRealization {K X : SSet.{u}}
    (D : K ⟶ X) (x : X _⦋0⦌) (H : SSet.Homotopy D (SSet.const x)) where
  cocone : JoinCocone D
  vertex : cocone.vertex = x
  family : (Δ[1] : SSet.{u}) ⊗ join K Δ[0] ⟶ X
  start : prismEndpoint 0 _ ≫ family = cocone.val
  finish : prismEndpoint 1 _ ≫ family = SSet.const x
  diagram : (Δ[1] ◁ joinInl K Δ[0]) ≫ family = (β_ (Δ[1] : SSet.{u}) K).hom ≫ H.h
  fixedVertex : (Δ[1] ◁ joinInr K Δ[0]) ≫ family = snd Δ[1] Δ[0] ≫ SSet.const x

/-- 元の指定自然変換を、同じ図式と同じ頂点の native な全余錐へ実現できる。 -/
lemma homotopyConstCoconeRealization_nonempty {K X : SSet.{u}} [Quasicategory X]
    (D : K ⟶ X) (x : X _⦋0⦌) (H : SSet.Homotopy D (SSet.const x)) :
    Nonempty (HomotopyConstCoconeRealization D x H) := by
  let Z : join K (Δ[0] : SSet.{u}) ⟶ X := SSet.const x
  let J := (β_ (Δ[1] : SSet.{u}) K).hom ≫ H.h
  have hJ : prismEndpoint 1 K ≫ J = joinInl K Δ[0] ≫ Z := by
    have ht : prismEndpoint 1 K ≫ (β_ (Δ[1] : SSet.{u}) K).hom = SSet.ι₁ := rfl
    dsimp only [J, Z]
    rw [← Category.assoc, ht, H.h₁, SSet.comp_const]
  obtain ⟨L, hL, hLK, hLv⟩ := exists_cocone_fixedVertex_prism Z J hJ
  have hd : joinInl K (Δ[0] : SSet.{u}) ≫ (prismEndpoint 0 _ ≫ L) = D := by
    rw [← Category.assoc, ← prismEndpoint_naturality, Category.assoc, hLK]
    have ht : prismEndpoint 0 K ≫ (β_ (Δ[1] : SSet.{u}) K).hom = SSet.ι₀ := rfl
    dsimp only [J]
    rw [← Category.assoc, ht, H.h₀]
  let c : JoinCocone D := ⟨prismEndpoint 0 _ ≫ L, hd⟩
  have hv : c.vertex = x := by
    rw [JoinCocone.vertex_eq]
    change SSet.yonedaEquiv (joinInr K (Δ[0] : SSet.{u}) ≫ (prismEndpoint 0 _ ≫ L)) = x
    rw [← Category.assoc, ← prismEndpoint_naturality, Category.assoc, hLv]
    simp only [Z, SSet.comp_const]
    rw [← SSet.yonedaEquiv_symm_zero, Equiv.apply_symm_apply]
  exact ⟨⟨c, hv, L, rfl, hL, hLK, by simpa only [Z, SSet.comp_const] using hLv⟩⟩

end SerrePositivity.InfinityCategories.F2.Ind
