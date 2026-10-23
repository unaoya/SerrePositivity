module

public import SerrePositivity.InfinityCategories.F1B.MappingParameters
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.MappingSpacePrisms
public import SerrePositivity.InfinityCategories.Core.PinchedUniversal
public import SerrePositivity.InfinityCategories.Core.FatJoinComparisonEpi

/-!
概要：右 pinched 写像空間から区間模型への比較射と単射性。
方針：F1 の右模型の計算を狭い依存上で用い、相対 join 延長に接続する。
規約：左模型・straightening のモジュールを import しない。
使われ方：Kerodon §4.6.5–4.6.6、Prop 6.2.1.17 の pinched 模型への移行。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.PinchedInterval

/-- 概要：標準零単体の点への定値射の後に頂点の Yoneda 射を続けるとその頂点に定値。
方針：定値射の後合成と零次の Yoneda の往復を使う。
規約：始域 A は任意。
使われ方：Kerodon §4.6.5、付加した点上の端点の計算。 -/
lemma const_point_comp_yoneda {A X : SSet.{u}} (x : X _⦋0⦌) :
    (SSet.const (stdSimplex.obj₀Equiv.symm 0) : A ⟶ Δ[0]) ≫ SSet.yonedaEquiv.symm x =
      SSet.const x := by
  rw [SSet.const_comp]
  have he : stdSimplex.obj₀Equiv.symm (0 : Fin 1) =
      SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) :=
    stdSimplex.obj₀Equiv.injective (by
      apply Fin.ext
      have h := (stdSimplex.obj₀Equiv (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})))).isLt
      have h' := (stdSimplex.obj₀Equiv (stdSimplex.obj₀Equiv.symm (0 : Fin 1))).isLt
      omega)
  rw [he]
  change SSet.const (SSet.yonedaEquiv (SSet.yonedaEquiv.symm x)) = SSet.const x
  rw [Equiv.apply_symm_apply]

/-- 概要：右 pinched 写像空間から両端固定の区間模型への比較射。
方針：恒等族を join 上に展開し、右の円筒比較で引き戻す。
規約：標的の quasicategory 性を要求しない。
使われ方：Kerodon §4.6.5–4.6.6、右模型と区間模型の比較。 -/
noncomputable def comparison {X : SSet.{u}} (x y : X _⦋0⦌) :
    pinchedHom x y ⟶ intervalMappingSpace x y :=
  intervalFamilyCurry
    (rightMappingSpacePrism (pinchedHom x y) ≫ pinchedHomUncurry (𝟙 (pinchedHom x y))) (by
      rw [← Category.assoc, rightMappingSpacePrism_zero, pinchedHomUncurry_inl]) (by
      rw [← Category.assoc, rightMappingSpacePrism_one, Category.assoc,
        pinchedHomUncurry_inr, const_point_comp_yoneda])

/-- 概要：右模型の比較射は任意の族を円筒比較で引き戻す操作を表す。
方針：区間模型の展開の自然性、円筒の自然性、join 図式への展開の自然性を使う。
規約：任意のパラメータ A と族 f を扱う。
使われ方：Kerodon §4.6.6、右模型の比較の相対的な持ち上げ。 -/
lemma comparison_uncurry {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ pinchedHom x y) :
    intervalMappingUncurry (f ≫ comparison x y) =
      rightMappingSpacePrism A ≫ pinchedHomUncurry f := by
  rw [intervalMappingUncurry_precomp]
  unfold comparison
  rw [intervalFamilyUncurry_curry, ← Category.assoc,
    rightMappingSpacePrism_naturality, Category.assoc, ← pinchedHomUncurry_precomp,
    Category.comp_id]

/-- 概要：右の点で等しい join 図式は右円筒への引き戻しで区別できる。
方針：点を補う直積の射の同型性で円柱を回収し、fat join のエピな比較を消去する。
規約：A が空の場合も右の点での等式を明示する。
使われ方：Kerodon §4.6.5–4.6.6、右 pinched 模型の比較の単射性。 -/
lemma rightMappingSpacePrism_hom_ext {A X : SSet.{u}} {f g : join A (Δ[0] : SSet.{u}) ⟶ X}
    (h : rightMappingSpacePrism A ≫ f = rightMappingSpacePrism A ≫ g)
    (hy : joinInr A Δ[0] ≫ f = joinInr A Δ[0] ≫ g) : f = g := by
  let l : Δ[1] ⊗ A ⟶ (A ⊗ Δ[1]) ⊗ (Δ[0] : SSet.{u}) :=
    (β_ Δ[1] A).hom ≫
      lift (𝟙 (A ⊗ Δ[1])) (SSet.const (stdSimplex.obj₀Equiv.symm 0))
  have hi : IsIso (lift (𝟙 (A ⊗ Δ[1]))
      (SSet.const (stdSimplex.obj₀Equiv.symm 0)) :
      A ⊗ Δ[1] ⟶ (A ⊗ Δ[1]) ⊗ (Δ[0] : SSet.{u})) :=
    IsIso.of_isIso_fac_right (lift_fst _ _)
  have : Epi l := by dsimp [l]; infer_instance
  have hc : joinCylinderMap A Δ[0] ≫ f = joinCylinderMap A Δ[0] ≫ g := by
    apply (cancel_epi l).1
    exact h
  apply (cancel_epi (fatJoinComparison A Δ[0])).1
  apply fatJoin_hom_ext
  · simpa only [← Category.assoc, fatJoinCylinder_comparison] using hc
  · have hh := congrArg (fun z ↦ prismEndpoint 0 A ≫ z) h
    simpa only [← Category.assoc, rightMappingSpacePrism_zero,
      fatJoinInl_comparison] using hh
  · simpa only [← Category.assoc, fatJoinInr_comparison] using hy

/-- 概要：右 pinched 模型から区間模型への比較射は単射。
方針：任意の族を join 図式に展開し、右円筒の外延性で比較する。
規約：X の Kan 性も quasicategory 性も不要。
使われ方：Kerodon §4.6.5–4.6.6、右模型を区間模型への包含として扱う。 -/
instance comparison_mono {X : SSet.{u}} (x y : X _⦋0⦌) :
    Mono (comparison x y) := by
  constructor
  intro A f g h
  apply pinchedHomUncurry_injective x y
  apply rightMappingSpacePrism_hom_ext
  · have hh := congrArg intervalMappingUncurry h
    simpa only [comparison_uncurry] using hh
  · rw [pinchedHomUncurry_inr, pinchedHomUncurry_inr]


end SerrePositivity.InfinityCategories.PinchedInterval
