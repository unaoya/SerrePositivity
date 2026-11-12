module

public import SerrePositivity.KST.Spectra.PointedMappingComponents

/-!
概要：球面から Kan 複体への点つき写像空間の連結成分と正次数ホモトピー群の同値。
方針：相対単体ホモトピーと球面のホモトピーの比較で、頂点の類を π₀ へ降ろす。
規約：ここでは集合の同値。群の積との追加の整合性は別途扱う。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。円の自己射の写像空間での作用。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.SphereSimplex

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：球面からの二つの射の類が等しいことと、写像空間の成分が等しいことは同値。
方針：単体の相対ホモトピーを商へ降ろし、逆向きは商から引き戻す。
規約：次元 n+1 は正。写像空間の頂点はパラメータ族で表示する。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。π₀ から正次数の群への降下。 -/
theorem class_eq_iff_components (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n : ℕ)
    (f g : PointedSimplicialSet.sphere.{u} (n + 1) ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (equiv Y (n + 1) f) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (equiv Y (n + 1) g) ↔
      π₀.mk (PointedMapping.familyVertex f) = π₀.mk (PointedMapping.familyVertex g) := by
  obtain ⟨s, rfl⟩ := (equiv Y (n + 1)).symm.surjective f
  obtain ⟨t, rfl⟩ := (equiv Y (n + 1)).symm.surjective g
  simp only [Equiv.apply_symm_apply]
  constructor
  · intro h
    obtain ⟨H⟩ := (KanHomotopyGroup.mk_eq_iff_relativeHomotopy s t).1 h
    exact (PointedMapping.piZero_eq_iff_pointedHomotopy _ _).2
      ⟨homotopy Y (n + 1) H, base_descendHomotopy Y (n + 1) H⟩
  · intro h
    obtain ⟨H, hH⟩ := (PointedMapping.piZero_eq_iff_pointedHomotopy _ _).1 h
    have r := pullHomotopy Y (n + 1) ((equiv Y (n + 1)).symm s)
      ((equiv Y (n + 1)).symm t) H hH
    simp only [Equiv.apply_symm_apply] at r
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.eq_of_relativeHomotopy r

/-- 概要：球面の写像空間の成分を正次数ホモトピー群へ送る。
方針：頂点を点つき射へ戻し、その単体の類を取り、辺のホモトピーで π₀ へ降ろす。
規約：標的は Kan。球面の次元は n+1。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。写像空間のホモトピー群の代表計算。 -/
def componentClass (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n : ℕ) :
    π₀ (PointedObject.basedHom (PointedSimplicialSet.sphere.{u} (n + 1)) Y).right →
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right n Y.basepoint :=
  π₀.lift (fun v ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk
    (equiv Y (n + 1) (PointedMapping.familyMap _ Y v))) (by
      intro v w e
      apply (class_eq_iff_components Y n _ _).2
      simpa only [PointedMapping.familyVertex_familyMap] using π₀.sound e)

/-- 概要：球面の写像空間の成分の類を、その射の代表で計算する。
方針：π₀ の lift と頂点表示の逆関係を使う。
規約：任意の球面からの点つき射。
使われ方：Goerss–Jardine I §7。比較同値の標準代表における計算。 -/
@[simp]
theorem componentClass_familyVertex (Y : PointedSimplicialSet.{u}) [KanComplex Y.right]
    (n : ℕ) (f : PointedSimplicialSet.sphere.{u} (n + 1) ⟶ Y) :
    componentClass Y n (π₀.mk (PointedMapping.familyVertex f)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (equiv Y (n + 1) f) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (equiv Y (n + 1)
    (PointedMapping.familyMap _ Y (PointedMapping.familyVertex f))) = _
  rw [PointedMapping.familyMap_familyVertex]

/-- 概要：球面の写像空間の成分から群への写像は全単射。
方針：群の元を境界定数単体で表し、単射性は二つの代表の類の比較へ戻す。
規約：群の積との整合性はこの集合の全単射性には含めない。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。球面による正次数の代表可能性。 -/
theorem componentClass_bijective (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n : ℕ) :
    Function.Bijective (componentClass Y n) := by
  constructor
  · intro a b h
    obtain ⟨v, rfl⟩ := π₀.mk_surjective a
    obtain ⟨w, rfl⟩ := π₀.mk_surjective b
    have hc := (class_eq_iff_components Y n
      (PointedMapping.familyMap _ Y v) (PointedMapping.familyMap _ Y w)).1 h
    simpa only [PointedMapping.familyVertex_familyMap] using hc
  · intro a
    obtain ⟨s, rfl⟩ := Quotient.mk_surjective a
    refine ⟨π₀.mk (PointedMapping.familyVertex ((equiv Y (n + 1)).symm s)), ?_⟩
    rw [componentClass_familyVertex, Equiv.apply_symm_apply]
    rfl

/-- 概要：球面の写像空間の連結成分と正次数ホモトピー群の標準的な集合の同値。
方針：代表を計算する写像の全単射性を使う。
規約：実際の球面の次元は n+1。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。有理化の写像空間の計算。 -/
def componentEquiv (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n : ℕ) :
    π₀ (PointedObject.basedHom (PointedSimplicialSet.sphere.{u} (n + 1)) Y).right ≃
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right n Y.basepoint :=
  Equiv.ofBijective _ (componentClass_bijective Y n)

/-- 概要：球面の成分から群への比較は標的の点つき Kan 射に関して自然。
方針：各成分を一つの射で表し、頂点の後合成と単体の後合成を計算する。
規約：両方の標的は Kan。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。写像空間での演算と群の演算の比較。 -/
theorem componentClass_natural {Y Z : PointedSimplicialSet.{u}}
    [KanComplex Y.right] [KanComplex Z.right] (n : ℕ) (p : Y ⟶ Z)
    (a : π₀ (PointedObject.basedHom (PointedSimplicialSet.sphere.{u} (n + 1)) Y).right) :
    componentClass Z n (mapπ₀ (PointedObject.basedHomMap _ p).right a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map p.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p)
        (componentClass Y n a) := by
  obtain ⟨v, rfl⟩ := π₀.mk_surjective a
  obtain ⟨f, rfl⟩ := (PointedMapping.familyVertexEquiv
    (PointedSimplicialSet.sphere.{u} (n + 1)) Y).surjective v
  change componentClass Z n (mapπ₀ (PointedObject.basedHomMap _ p).right
    (π₀.mk (PointedMapping.familyVertex f))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map p.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p)
        (componentClass Y n (π₀.mk (PointedMapping.familyVertex f)))
  rw [mapπ₀_mk, PointedMapping.familyVertex_post, componentClass_familyVertex,
    componentClass_familyVertex, equiv_comp]
  rfl

end

end SerrePositivity.KST.Spectra.SphereSimplex
