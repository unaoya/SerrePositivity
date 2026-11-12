module

public import SerrePositivity.KST.Spectra.AnodyneCofiberSource

/-!
概要：相対三角形からの写像空間の実際の基点固定収縮。
方針：終対象への射の全単射 RLP から恒等射と零射の間の相対ホモトピーを充填する。
規約：群の消滅だけから収縮を推論しない。
使われ方：Goerss–Jardine I §7、BF 1978 §2。二つの三角形の差の符号の比較。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.SimplicialModel
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：終対象への全単射 RLP を持つ点つき対象は基点を固定して収縮する。
方針：基点包含を固定する恒等射と零射の垂直ホモトピーを充填する。
規約：収縮は実際の区間のホモトピーである。
使われ方：Goerss–Jardine I §7、HTT A.3.3。写像空間の指定した収縮。 -/
theorem exists_basedContraction_of_terminal_rlp (E : PointedSimplicialSet.{u})
    (hp : (MorphismProperty.monomorphisms SSet.{u}).rlp (terminal.from E.right)) :
    ∃ H : SSet.Homotopy (𝟙 E.right) (0 : E ⟶ E).right,
      E.hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ E.hom := by
  let : Mono E.hom := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basepoint_mono E
  let f : E ⟶ E := 𝟙 E
  let g : E ⟶ E := 0
  have hbase : E.hom ≫ f.right = E.hom ≫ g.right := by rw [Under.w f, Under.w g]
  obtain ⟨H, _, hH⟩ := MonoRightLiftingRelativeHomotopy.exists_relative_vertical_homotopy
    (terminal.from E.right) hp E.hom f.right g.right (Subsingleton.elim _ _) hbase
  refine ⟨H, ?_⟩
  rw [hH, Under.w f]
  rfl

/-- 概要：anodyne な基点包含を持つ源からの Kan 値写像空間は基点固定で収縮する。
方針：点への制限から得た全単射 RLP に収縮の充填を適用する。
規約：写像空間の基点は零射。
使われ方：Goerss–Jardine I §7、BF 1978 §2。相対単体の充填の差を比較する。 -/
theorem PointedMapping.exists_contraction_of_basepoint_anodyne
    (A Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (hA : anodyneExtensions A.hom) :
    ∃ H : SSet.Homotopy (𝟙 (PointedObject.basedHom A Y).right)
      (0 : PointedObject.basedHom A Y ⟶ PointedObject.basedHom A Y).right,
      (PointedObject.basedHom A Y).hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ (PointedObject.basedHom A Y).hom :=
  exists_basedContraction_of_terminal_rlp _ (terminal_rlp_of_basepoint_anodyne A Y hA)

/-- 概要：相対三角形からの Kan 値写像空間は基点を固定して収縮する。
方針：ホーンの cofiber の基点の anodyne 性を使う。
規約：収縮の区間と基点固定式を明示する。
使われ方：Goerss–Jardine I §7、BF 1978 §2。正方形の二つの三角形の符号の比較。 -/
theorem triangleDiskHom_exists_contraction (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] :
    ∃ H : SSet.Homotopy (𝟙 (PointedObject.basedHom triangleDisk.{u} Y).right)
      (0 : PointedObject.basedHom triangleDisk.{u} Y ⟶
        PointedObject.basedHom triangleDisk Y).right,
      (PointedObject.basedHom triangleDisk Y).hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫
          (PointedObject.basedHom triangleDisk Y).hom :=
  PointedMapping.exists_contraction_of_basepoint_anodyne _ Y triangleDisk_basepoint_anodyne

end

end SerrePositivity.KST.Spectra
