module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpacePrisms
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CosliceFiberUniversal
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.PinchedUniversal
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：左右の pinched 写像空間から両端固定の区間模型への比較射。
方針：族を join の図式へ展開し、自然な円筒比較で引き戻して curry する。
規約：左側は coslice fiber の厳密な同型を使い、比較射の同値性は後続で証明する。
使われ方：Kerodon §4.6.5（Tag 01KW）–4.6.6（Tag 04HY）、unstraightening の fiber 比較の中間射。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：定値な両端の区間境界図式は境界の指定射の第一射影による引き戻し。
方針：境界の各単体の値で分岐する二つの定義を比較する。
規約：パラメータ A の情報は忘れる。
使われ方：Kerodon §4.6.6（Tag 04HY）、端点による境界条件の確認。 -/
lemma intervalMappingBoundary_diagram {A X : SSet.{u}} (x y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram (SSet.const x : A ⟶ X) (SSet.const y) =
      fst (boundary 1 : SSet.{u}) A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingBoundary x y := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- 概要：定値な端点を持つ区間の族を写像空間へ curry する。
方針：両端から境界の条件を復元して、区間模型の普遍性を適用する。
規約：時刻零が x、時刻一が y。
使われ方：Kerodon §4.6.6（Tag 04HY）、左右の join の円筒の比較射の作成。 -/
noncomputable def intervalMappingCurryOfEndpoints {A X : SSet.{u}} {x y : X _⦋0⦌}
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ X)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ H = SSet.const x)
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ H = SSet.const y) : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingCurry H (by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_restrict, h₀, h₁, intervalMappingBoundary_diagram])

/-- 概要：端点条件から curry した族を展開すると元の区間の族。
方針：境界条件を用いた curry の往復を使う。
規約：端点条件の証明の選択には依存しない。
使われ方：Kerodon §4.6.6（Tag 04HY）、比較射の族の計算。 -/
lemma intervalMappingUncurry_curryOfEndpoints {A X : SSet.{u}} {x y : X _⦋0⦌}
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ X)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ H = SSet.const x)
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ H = SSet.const y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (intervalMappingCurryOfEndpoints H h₀ h₁) = H :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_curry _ _

/-- 概要：標準零単体の点への定値射の後に頂点の Yoneda 射を続けるとその頂点に定値。
方針：定値射の後合成と零次の Yoneda の往復を使う。
規約：始域 A は任意。
使われ方：Kerodon §4.6.5（Tag 01KW）、付加した点上の端点の計算。 -/
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
使われ方：Kerodon §4.6.5（Tag 01KW）–4.6.6（Tag 04HY）、右模型と区間模型の比較。 -/
@[kerodon 01L2]
noncomputable def pinchedHomToIntervalMappingSpace {X : SSet.{u}} (x y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y :=
  intervalMappingCurryOfEndpoints
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y))) (by
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry_inl]) (by
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism_one, Category.assoc,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry_inr, const_point_comp_yoneda])

/-- 概要：coslice fiber から両端固定の区間模型への比較射。
方針：恒等族を左に点を持つ join 上に展開し、左の円筒比較で引き戻す。
規約：左 pinched 模型との同型により、左模型の比較射も与える。
使われ方：Kerodon §4.6.5（Tag 01KW）–4.6.6（Tag 04HY）、left unstraightening の fiber の比較。 -/
noncomputable def cosliceFiberToIntervalMappingSpace {X : SSet.{u}} (x y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y :=
  intervalMappingCurryOfEndpoints
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingSpacePrism _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberUncurry (𝟙 _)) (by
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingSpacePrism_zero, Category.assoc,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberUncurry_inl, const_point_comp_yoneda]) (by
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingSpacePrism_one, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberUncurry_inr])

/-- 概要：左 pinched 写像空間から区間模型への比較射。
方針：coslice fiber との同型の逆を既存の区間比較へ続ける。
規約：端点の順序は x から y のまま。
使われ方：Kerodon §4.6.5（Tag 01KW）–4.6.6（Tag 04HY）、左右の写像空間の比較。 -/
@[kerodon 01L2]
noncomputable def pinchedHomLeftToIntervalMappingSpace {X : SSet.{u}} (x y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft x y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberPinchedLeftIso x y).inv ≫ cosliceFiberToIntervalMappingSpace x y

/-- 概要：右模型の比較射は任意の族を円筒比較で引き戻す操作を表す。
方針：区間模型の展開の自然性、円筒の自然性、join 図式への展開の自然性を使う。
規約：任意のパラメータ A と族 f を扱う。
使われ方：Kerodon §4.6.6（Tag 04HY）、右模型の比較の相対的な持ち上げ。 -/
lemma pinchedHomToIntervalMappingSpace_uncurry {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (f ≫ pinchedHomToIntervalMappingSpace x y) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry f := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]
  unfold pinchedHomToIntervalMappingSpace
  rw [intervalMappingUncurry_curryOfEndpoints, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism_naturality, Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry_precomp,
    Category.comp_id]

/-- 概要：coslice fiber の比較射は任意の族を左の円筒比較で引き戻す操作を表す。
方針：区間と coslice fiber の展開の自然性、および円筒比較の自然性を組み合わせる。
規約：任意のパラメータ A と fiber への族 f を扱う。
使われ方：Kerodon §4.6.6（Tag 04HY）、左模型の比較の相対的な持ち上げ。 -/
lemma cosliceFiberToIntervalMappingSpace_uncurry {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (f ≫ cosliceFiberToIntervalMappingSpace x y) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingSpacePrism A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberUncurry f := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]
  unfold cosliceFiberToIntervalMappingSpace
  rw [intervalMappingUncurry_curryOfEndpoints, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingSpacePrism_naturality, Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberUncurry_precomp,
    Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
