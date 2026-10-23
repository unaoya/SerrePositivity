module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.MappingCylinderGeneralComparison
public import SerrePositivity.InfinityCategories.F1.Scaffold.ScaffoldFiniteVerticalEdges

/-!
概要：有限鎖上の left scaffold の全空間比較の帰納ステップ。
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

/-- 概要：尾部への底変換の比較が前合成同値なら、有限鎖の left scaffold の全体の比較も前合成同値。
方針：標準円柱の比較を一般の写像円柱判定で同値とし、その inner anodyne な比較を消去する。
規約：係数値は Kan 複体、射影は left fibration。
使われ方：Kerodon Theorem 5.3.5.7、有限鎖上の全空間比較の帰納ステップ。 -/
lemma IsLeftScaffold.finiteComparison_step (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ nerve (ULift.{u} (Fin (n + 2)))) [LeftFibration p]
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)]
    (l : simplicialReplacement F ⟶ E) (hs : IsLeftScaffold p F l)
    (h : l ≫ p = simplicialReplacementProjection F)
    (ht : IsPrecompositionEquivalence (leftScaffoldBaseChange p F l h (scaffoldFiniteTail n))) :
    IsPrecompositionEquivalence l := by
  have : Quasicategory E := quasicategory_of_innerFibration p
  let f := scaffoldFiniteCylinderAttachingMap n F
  let H := scaffoldFiniteScaffoldPrism n F l
  let g := simplicialReplacementBaseMap (scaffoldFiniteTail n) F ≫ l
  let q := p ≫ scaffoldFiniteCollapse n
  have w : prismEndpoint 1 (F.obj (ULift.up 0)) ≫ H = f ≫ g := by
    have he := congrArg (fun k ↦ k ≫ l) (scaffoldFiniteCylinderComparison_endpoint_one n F)
    simpa only [H, f, g, scaffoldFiniteScaffoldPrism, Category.assoc] using he
  have hH : H ≫ q = fst Δ[1] (F.obj (ULift.up 0)) :=
    scaffoldFiniteScaffoldPrism_interval_projection n p F l h
  have hz0 : scaffoldFiniteZeroFiberComparison n p F l h ≫
      vertexFiberι q (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
        prismEndpoint 0 (F.obj (ULift.up 0)) ≫ H := by
    simpa only [H, scaffoldFiniteScaffoldPrism, Category.assoc] using
      scaffoldFiniteZeroFiberComparison_ι n p F l h
  have hz1 : scaffoldFiniteOneFiberComparison n p F l h ≫
      vertexFiberι q (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = g := by
    simpa only [g, ← Category.assoc, scaffoldFiniteCylinderComparison_inr] using
      scaffoldFiniteOneFiberComparison_ι n p F l h
  have hg : g ≫ q = SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
    rw [← hz1, Category.assoc, vertexFiberι_comp, SSet.comp_const]
  have h0 := hs.finiteZeroFiber_isPrecompositionEquivalence n h
  have h1 := (scaffoldFiniteOneFiberComparison_isPrecompositionEquivalence_iff n p F l h).mpr ht
  have hu := mappingCylinder_isPrecompositionEquivalence f q H g w hH hg
    (scaffoldFiniteZeroFiberComparison n p F l h) hz0
    (scaffoldFiniteOneFiberComparison n p F l h) hz1 h0 h1
    (scaffoldFiniteScaffoldPrism_vertical_isCocartesian n p F l h)
  have he : scaffoldFiniteCylinderComparison n F ≫ l = pushout.desc H g w := by
    apply pushout.hom_ext
    · rw [pushout.inl_desc]
      rfl
    · rw [← Category.assoc, scaffoldFiniteCylinderComparison_inr, pushout.inr_desc]
  apply (isPrecompositionEquivalence_scaffoldFiniteCylinderComparison n F).cancel_left
  rwa [he]

end SerrePositivity.InfinityCategories
