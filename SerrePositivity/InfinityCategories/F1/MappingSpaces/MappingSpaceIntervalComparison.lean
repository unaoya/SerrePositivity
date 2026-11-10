module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.MappingSpacePrisms
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.CosliceFiberUniversal
public import SerrePositivity.InfinityCategories.Core.PinchedUniversal
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：左右の pinched 写像空間から両端固定の区間模型への比較射。
方針：族を join の図式へ展開し、自然な円筒比較で引き戻して curry する。
規約：左側は coslice fiber の厳密な同型を使い、比較射の同値性は後続で証明する。
使われ方：Kerodon §4.6.5–4.6.6、unstraightening の fiber 比較の中間射。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：定値な両端の区間境界図式は境界の指定射の第一射影による引き戻し。
方針：境界の各単体の値で分岐する二つの定義を比較する。
規約：パラメータ A の情報は忘れる。
使われ方：Kerodon §4.6.6、端点による境界条件の確認。 -/
lemma intervalMappingBoundary_diagram {A X : SSet.{u}} (x y : X _⦋0⦌) :
    intervalBoundaryDiagram (SSet.const x : A ⟶ X) (SSet.const y) =
      fst (boundary 1 : SSet.{u}) A ≫ intervalMappingBoundary x y := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- 概要：定値な端点を持つ区間の族を写像空間へ curry する。
方針：両端から境界の条件を復元して、区間模型の普遍性を適用する。
規約：時刻零が x、時刻一が y。
使われ方：Kerodon §4.6.6、左右の join の円筒の比較射の作成。 -/
noncomputable def intervalMappingCurryOfEndpoints {A X : SSet.{u}} {x y : X _⦋0⦌}
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ X)
    (h₀ : prismEndpoint 0 A ≫ H = SSet.const x)
    (h₁ : prismEndpoint 1 A ≫ H = SSet.const y) : A ⟶ intervalMappingSpace x y :=
  intervalMappingCurry H (by
    rw [intervalBoundaryDiagram_restrict, h₀, h₁, intervalMappingBoundary_diagram])

/-- 概要：端点条件から curry した族を展開すると元の区間の族。
方針：境界条件を用いた curry の往復を使う。
規約：端点条件の証明の選択には依存しない。
使われ方：Kerodon §4.6.6、比較射の族の計算。 -/
lemma intervalMappingUncurry_curryOfEndpoints {A X : SSet.{u}} {x y : X _⦋0⦌}
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ X)
    (h₀ : prismEndpoint 0 A ≫ H = SSet.const x)
    (h₁ : prismEndpoint 1 A ≫ H = SSet.const y) :
    intervalMappingUncurry (intervalMappingCurryOfEndpoints H h₀ h₁) = H :=
  intervalMappingUncurry_curry _ _

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
@[kerodon 01L2]
noncomputable def pinchedHomToIntervalMappingSpace {X : SSet.{u}} (x y : X _⦋0⦌) :
    pinchedHom x y ⟶ intervalMappingSpace x y :=
  intervalMappingCurryOfEndpoints
    (rightMappingSpacePrism (pinchedHom x y) ≫ pinchedHomUncurry (𝟙 (pinchedHom x y))) (by
      rw [← Category.assoc, rightMappingSpacePrism_zero, pinchedHomUncurry_inl]) (by
      rw [← Category.assoc, rightMappingSpacePrism_one, Category.assoc,
        pinchedHomUncurry_inr, const_point_comp_yoneda])

/-- 概要：coslice fiber から両端固定の区間模型への比較射。
方針：恒等族を左に点を持つ join 上に展開し、左の円筒比較で引き戻す。
規約：左 pinched 模型との同型により、左模型の比較射も与える。
使われ方：Kerodon §4.6.5–4.6.6、left unstraightening の fiber の比較。 -/
noncomputable def cosliceFiberToIntervalMappingSpace {X : SSet.{u}} (x y : X _⦋0⦌) :
    vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y ⟶ intervalMappingSpace x y :=
  intervalMappingCurryOfEndpoints
    (leftMappingSpacePrism _ ≫ cosliceFiberUncurry (𝟙 _)) (by
      rw [← Category.assoc, leftMappingSpacePrism_zero, Category.assoc,
        cosliceFiberUncurry_inl, const_point_comp_yoneda]) (by
      rw [← Category.assoc, leftMappingSpacePrism_one, cosliceFiberUncurry_inr])

/-- 概要：左 pinched 写像空間から区間模型への比較射。
方針：coslice fiber との同型の逆を既存の区間比較へ続ける。
規約：端点の順序は x から y のまま。
使われ方：Kerodon §4.6.5–4.6.6、左右の写像空間の比較。 -/
@[kerodon 01L2]
noncomputable def pinchedHomLeftToIntervalMappingSpace {X : SSet.{u}} (x y : X _⦋0⦌) :
    pinchedHomLeft x y ⟶ intervalMappingSpace x y :=
  (cosliceFiberPinchedLeftIso x y).inv ≫ cosliceFiberToIntervalMappingSpace x y

/-- 概要：右模型の比較射は任意の族を円筒比較で引き戻す操作を表す。
方針：区間模型の展開の自然性、円筒の自然性、join 図式への展開の自然性を使う。
規約：任意のパラメータ A と族 f を扱う。
使われ方：Kerodon §4.6.6、右模型の比較の相対的な持ち上げ。 -/
lemma pinchedHomToIntervalMappingSpace_uncurry {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ pinchedHom x y) :
    intervalMappingUncurry (f ≫ pinchedHomToIntervalMappingSpace x y) =
      rightMappingSpacePrism A ≫ pinchedHomUncurry f := by
  rw [intervalMappingUncurry_precomp]
  unfold pinchedHomToIntervalMappingSpace
  rw [intervalMappingUncurry_curryOfEndpoints, ← Category.assoc,
    rightMappingSpacePrism_naturality, Category.assoc, ← pinchedHomUncurry_precomp,
    Category.comp_id]

/-- 概要：coslice fiber の比較射は任意の族を左の円筒比較で引き戻す操作を表す。
方針：区間と coslice fiber の展開の自然性、および円筒比較の自然性を組み合わせる。
規約：任意のパラメータ A と fiber への族 f を扱う。
使われ方：Kerodon §4.6.6、左模型の比較の相対的な持ち上げ。 -/
lemma cosliceFiberToIntervalMappingSpace_uncurry {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) :
    intervalMappingUncurry (f ≫ cosliceFiberToIntervalMappingSpace x y) =
      leftMappingSpacePrism A ≫ cosliceFiberUncurry f := by
  rw [intervalMappingUncurry_precomp]
  unfold cosliceFiberToIntervalMappingSpace
  rw [intervalMappingUncurry_curryOfEndpoints, ← Category.assoc,
    leftMappingSpacePrism_naturality, Category.assoc, ← cosliceFiberUncurry_precomp,
    Category.comp_id]

end SerrePositivity.InfinityCategories
