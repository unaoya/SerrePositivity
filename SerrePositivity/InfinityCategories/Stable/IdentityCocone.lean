module
public import SerrePositivity.InfinityCategories.Stable.Cocone
public import SerrePositivity.InfinityCategories.Core.InitialUniqueness
public import SerrePositivity.InfinityCategories.Core.PointHornJoin
public import SerrePositivity.InfinityCategories.Core.OuterHornDuality

/-! # 一点の恒等余錐の余極限性

概要：頂点 x から自身への恒等余錐は一点図式の余極限である。
方針：coslice の境界を最初の外側ホーンに直し、恒等な最初の辺の可逆性で充填する。
規約：余極限は既存の coslice の始対象としての定義を用いる。
使われ方：S4 の恒等射の cofiber 四角形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：一点の恒等余錐はその coslice の始対象である。
方針：境界の最初の余錐が恒等である条件を外側ホーンの可逆な最初の辺に移す。
規約：値域は quasicategory。使われ方：一点の余極限と恒等射の押し出し。 -/
lemma cosliceIdentityCone_isInitialVertex {X : SSet.{u}} [Quasicategory X] (x : X _⦋0⦌) :
    IsInitialVertex (X := sliceUnder (SSet.yonedaEquiv.symm x)) (cosliceIdentityCone x) := by
  intro n a ha
  let T := sliceUnderUncurry a
  let E := initialPointHornJoinIso.{u} (n + 1)
  let σ := E.inv ≫ T
  have hfirst : joinMap (𝟙 (Δ[0] : SSet.{u})) (boundaryVertex n 0) ≫ T = SSet.const x := by
    have h := congrArg sliceUnderUncurry ha
    rw [sliceUnderUncurry_precomp, sliceUnderUncurry_yoneda] at h
    exact h
  have heq : σ.app (Opposite.op ⦋1⦌) (initialHornEdge n) = PinchedHom.constant x 1 := by
    rw [← initialPointHornJoinIso_edge n, ← SSet.yonedaEquiv_comp]
    change SSet.yonedaEquiv
      (((joinStdSimplexIso 0 0).inv ≫ joinMap (𝟙 Δ[0]) (boundaryVertex n 0) ≫ E.hom) ≫
        (E.inv ≫ T)) = _
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [hfirst, SSet.comp_const]
    rfl
  let e := edgeOfSimplex (σ.app (Opposite.op ⦋1⦌) (initialHornEdge n))
  let d := SSet.Truncated.Edge.id (X := (truncation 2).obj X) x
  have hed : e.edge = d.edge := heq.trans (pinchedConstant_one x)
  have hd : IsInvertibleEdge d := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk d)
    have h := SSet.Truncated.HomotopyCategory.homMk_id (V := (truncation 2).obj X) x
    rw [h]
    infer_instance
  have he : IsInvertibleEdge e := (isInvertibleEdge_congr hed).mpr hd
  obtain ⟨F, hF⟩ := hasInitialHornFillers_of_isInvertibleEdge e he n σ rfl
  let J := (pointJoinStdSimplexIso (n + 1)).hom ≫ F
  have hJ : joinMap (𝟙 (Δ[0] : SSet.{u})) (boundary (n + 1)).ι ≫ J = T := by
    change (joinMap _ _ ≫ (pointJoinStdSimplexIso (n + 1)).hom) ≫ F = _
    rw [← initialPointHornJoinIso_hom_ι, Category.assoc, hF]
    exact E.hom_inv_id_assoc T
  have hfix : joinInl (Δ[0] : SSet.{u}) Δ[n + 1] ≫ J = SSet.yonedaEquiv.symm x := by
    calc
      _ = joinInl (Δ[0] : SSet.{u}) (boundary (n + 1) : SSet.{u}) ≫
          joinMap (𝟙 Δ[0]) (boundary (n + 1)).ι ≫ J := by
        symm
        rw [← Category.assoc, joinInl_joinMap, Category.id_comp]
      _ = _ := by rw [hJ]; exact sliceUnderUncurry_fixed a
  refine ⟨sliceUnderCurry J hfix, ?_⟩
  apply sliceUnderUncurry_injective
  rw [sliceUnderUncurry_precomp, sliceUnderUncurry_curry]
  exact hJ

/-- 概要：一点図式の恒等余錐は余極限である。
方針：coslice の恒等頂点の始対象性を余極限の定義として読む。
規約：恒等余錐の実際の射は定値射。使われ方：退化四角形の普遍性。 -/
lemma cosliceIdentityCone_isColimit {X : SSet.{u}} [Quasicategory X] (x : X _⦋0⦌) :
    IsColimitCone (show JoinCocone (SSet.yonedaEquiv.symm x) from cosliceIdentityCone x) :=
  cosliceIdentityCone_isInitialVertex x

/-- 概要：定値写像で与えられた一点図式の余錐は余極限である。
方針：固定条件から基底の頂点を同定し、恒等余錐に帰着する。
規約：基底の射は任意の表示を許す。使われ方：退化余錐の判定。 -/
lemma isColimitCone_of_point_constant {X : SSet.{u}} [Quasicategory X]
    {p : (Δ[0] : SSet.{u}) ⟶ X} (c : JoinCocone p) (x : X _⦋0⦌)
    (h : c.val = SSet.const x) : IsColimitCone c := by
  have hp : p = SSet.yonedaEquiv.symm x := by
    rw [← c.property, h, SSet.comp_const, SSet.yonedaEquiv_symm_zero]
  subst p
  have he : c = cosliceIdentityCone x := Subtype.ext h
  rw [he]
  exact cosliceIdentityCone_isColimit x

end SerrePositivity.InfinityCategories
