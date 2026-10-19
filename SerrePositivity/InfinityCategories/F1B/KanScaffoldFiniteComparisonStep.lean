module

public import SerrePositivity.InfinityCategories.F1B.KanSectionMappingCylinderGeneralComparison
public import SerrePositivity.InfinityCategories.F1B.KanScaffoldFiniteVerticalEdges

/-!
概要：有限鎖上の cocartesian scaffold の全空間比較の帰納ステップ。
方針：最初の係数と尾部を写像円柱で結び、両端の比較と cocartesian な垂直辺の条件を適用する。
規約：尾部の replacement の quasicategory 性は要求しない。
使われ方：Kerodon Theorem 5.3.5.7、Theorem 5.2.4.1 による有限次元の帰納。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：尾部への底変換の比較が前合成同値なら、有限鎖の cocartesian scaffold の全体の比較も前合成同値。
方針：標準円柱の比較を一般の写像円柱判定で同値とし、その inner anodyne な比較を消去する。
規約：係数値は quasicategory、射影は cocartesian fibration。
使われ方：Kerodon Theorem 5.3.5.7、有限鎖上の全空間比較の帰納ステップ。 -/
lemma KanCocartesianScaffold.finiteComparison_step (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ nerve (ULift.{u} (Fin (n + 2)))) [CocartesianFibration p]
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) [∀ c, Quasicategory (F.obj c)]
    (l : simplicialReplacement F ⟶ E) (hs : KanCocartesianScaffold p F l)
    (h : l ≫ p = simplicialReplacementProjection F)
    (ht : IsPrecompositionEquivalence (kanScaffoldBaseChange p F l h (scaffoldFiniteTail n))) :
    IsPrecompositionEquivalence l := by
  have : Quasicategory E := quasicategory_of_innerFibration p
  let f := scaffoldFiniteCylinderAttachingMap n F
  let H := kanScaffoldFiniteScaffoldPrism n F l
  let g := simplicialReplacementBaseMap (scaffoldFiniteTail n) F ≫ l
  let q := p ≫ scaffoldFiniteCollapse n
  have w : prismEndpoint 1 (F.obj (ULift.up 0)) ≫ H = f ≫ g := by
    have he := congrArg (fun k ↦ k ≫ l) (kanScaffoldFiniteCylinderComparison_endpoint_one n F)
    simpa only [H, f, g, kanScaffoldFiniteScaffoldPrism, Category.assoc] using he
  have hH : H ≫ q = fst Δ[1] (F.obj (ULift.up 0)) :=
    kanScaffoldFiniteScaffoldPrism_interval_projection n p F l h
  have hz0 : kanScaffoldFiniteZeroFiberComparison n p F l h ≫
      vertexFiberι q (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
        prismEndpoint 0 (F.obj (ULift.up 0)) ≫ H := by
    simpa only [H, kanScaffoldFiniteScaffoldPrism, Category.assoc] using
      kanScaffoldFiniteZeroFiberComparison_ι n p F l h
  have hz1 : kanScaffoldFiniteOneFiberComparison n p F l h ≫
      vertexFiberι q (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = g := by
    simpa only [g, ← Category.assoc, scaffoldFiniteCylinderComparison_inr] using
      kanScaffoldFiniteOneFiberComparison_ι n p F l h
  have hg : g ≫ q = SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
    rw [← hz1, Category.assoc, vertexFiberι_comp, SSet.comp_const]
  have h0 := hs.finiteZeroFiber_isPrecompositionEquivalence n h
  have h1 := (kanScaffoldFiniteOneFiberComparison_isPrecompositionEquivalence_iff n p F l h).mpr ht
  have hu := KanSection.mappingCylinder_isPrecompositionEquivalence f q H g w hH hg
    (kanScaffoldFiniteZeroFiberComparison n p F l h) hz0
    (kanScaffoldFiniteOneFiberComparison n p F l h) hz1 h0 h1
    (kanScaffoldFiniteScaffoldPrism_vertical_isCocartesian n p F l h hs.horizontal)
  have he : scaffoldFiniteCylinderComparison n F ≫ l = pushout.desc H g w := by
    apply pushout.hom_ext
    · rw [pushout.inl_desc]
      rfl
    · rw [← Category.assoc, scaffoldFiniteCylinderComparison_inr, pushout.inr_desc]
  apply (isPrecompositionEquivalence_scaffoldFiniteCylinderComparison n F).cancel_left
  rwa [he]

end SerrePositivity.InfinityCategories
