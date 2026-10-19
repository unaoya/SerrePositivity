module

public import SerrePositivity.InfinityCategories.F2.CoherentVertices

/-!
概要：通常の順序圏上の図式を simplicial thickening 上の豊穣関手へ送る。
方針：順方向の Hom は図式の射に定値とし、逆方向の Hom の空性で構造則を閉じる。
規約：元の単体的圏の通常の射との整合性を用い、局所 Kan 性は不要。
使われ方：coherent nerve 内に指定射の辺と厳密な合成図式を構成する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe v u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory
namespace SerrePositivity.InfinityCategories.F2

variable {C : Type u} [Category.{v} C] [SimplicialCategory C]
variable {J : Type v} [LinearOrder J]

/-- 概要：順序図式の一つの Hom を豊穣 Hom への写像にする。
方針：順方向では元の射の零単体に定値とし、逆方向では空の Hom から写す。
規約：a≤b の証明の違いは通常の順序圏の射の一意性で消える。
使われ方：順序図式の豊穣化の Hom 成分。 -/
def coherentOrderHomMap (F : J ⥤ C) (a b : J) :
    nerve (SimplicialThickening.Path a b) ⟶ SimplicialCategory.sHom (F.obj a) (F.obj b) :=
  if h : a ≤ b then toUnit _ ≫ eHomEquiv SSet (F.map (homOfLE h))
  else Coherent.pathEmptyHom a b h _

/-- 概要：通常の順序図式は simplicial thickening からの豊穣関手を与える。
方針：Hom を定値に写し、元の図式の合成則と空の Hom の一意性を使う。
規約：高次の比較は恒等であり、任意の coherent 図式の読み戻しは主張しない。
使われ方：通常の射とその合成を coherent nerve 内で具体化する。 -/
def coherentOrderDiagram (F : J ⥤ C) :
    EnrichedFunctor SSet (SimplicialThickening J) C where
  obj a := F.obj a.as
  map a b := coherentOrderHomMap F a.as b.as
  map_id a := by
    simp only [coherentOrderHomMap, dite_eq_left le_rfl, homOfLE_refl, F.map_id,
      eHomEquiv_id]
    rw [← Category.assoc]
    have h : eId SSet a ≫ toUnit (nerve (SimplicialThickening.Path a.as a.as)) = 𝟙 _ :=
      toUnit_unique _ _
    rw [h, Category.id_comp]
  map_comp a b c := by
    by_cases hab : a.as ≤ b.as
    · by_cases hbc : b.as ≤ c.as
      · have hac := hab.trans hbc
        simp only [coherentOrderHomMap, dite_eq_left hab, dite_eq_left hbc, dite_eq_left hac]
        rw [← tensorHom_comp_tensorHom, Category.assoc]
        have hi :
            (eHomEquiv SSet (F.map (homOfLE hab)) ⊗ₘ
              eHomEquiv SSet (F.map (homOfLE hbc))) ≫
                eComp SSet (F.obj a.as) (F.obj b.as) (F.obj c.as) =
            (λ_ (𝟙_ SSet)).hom ≫ eHomEquiv SSet (F.map (homOfLE hac)) := by
          apply (cancel_epi (λ_ (𝟙_ SSet)).inv).mp
          simp only [Iso.inv_hom_id_assoc]
          rw [← eHomEquiv_comp, ← F.map_comp]
          rfl
        rw [hi, ← Category.assoc]
        have ht :
            eComp SSet a b c ≫ toUnit (nerve (SimplicialThickening.Path a.as c.as)) =
            (toUnit (nerve (SimplicialThickening.Path a.as b.as)) ⊗ₘ
              toUnit (nerve (SimplicialThickening.Path b.as c.as))) ≫
                (λ_ (𝟙_ SSet)).hom := toUnit_unique _ _
        simpa only [Category.assoc] using
          congrArg (fun k ↦ k ≫ eHomEquiv SSet (F.map (homOfLE hac))) ht
      · exact Coherent.pathProduct_empty_hom_ext a.as b.as c.as (Or.inr hbc) _ _
    · exact Coherent.pathProduct_empty_hom_ext a.as b.as c.as (Or.inl hab) _ _

end SerrePositivity.InfinityCategories.F2
