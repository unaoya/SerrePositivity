module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FixedEndpointFatComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceIntervalComparison

/-!
概要：両端固定の fat join の錐の空間の任意パラメータでの普遍性。
方針：太い slice の curry と uncurry を両端固定の fiber に制限する。
規約：左端は指定頂点に定値、右端は元の図式に厳密に一致させる。
使われ方：Kerodon §4.6.6（Tag 04HY）、7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の固定頂点を保つ逆射の構成。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：両端固定の fat join の錐の空間は Kan 複体。
方針：通常の join の模型との圏同値をホモトピー圏へ移し、亜群性から Kan 性を得る。
規約：X は quasicategory でよく、K は任意である。
使われ方：Kerodon §4.6.6（Tag 04HY）、固定頂点を保つホモトピーを関手の同型へ移す。
-/
instance fixedEndpointFatConeSpace_kanComplex {K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (x : X _⦋0⦌) : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedEndpointFatConeSpace p x) := by
  let e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedEndpointConeFatComparison_isQCatEquivalence p x).choose.toHoEquivalence
  have : IsGroupoid (hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedEndpointConeSpace p x)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.kanComplex_ho_isGroupoid _
  have : IsGroupoid (hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedEndpointFatConeSpace p x)) :=
    isGroupoid_of_reflects_iso e.inverse
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromCategoriesToSimplicialSets.kanComplex_of_isGroupoid _

/-- 概要：両端固定の fat join の錐の右端は元の図式に定値。
方針：固定した両端の図式を右包含へ制限する。
規約：充填性の仮定は不要。
使われ方：Kerodon §4.6.6（Tag 04HY） の太い slice への忘却射。 -/
lemma fixedFatConeSpace_inr {K X : SSet.{u}} (p : K ⟶ X) (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinEndpointInclusion (Δ[0] : SSet.{u}) K)).app X)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc (SSet.yonedaEquiv.symm x) p)) ≫
      (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr Δ[0] K)).app X = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedDiagramι_pre_factor (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinEndpointInclusion (Δ[0] : SSet.{u}) K)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc (SSet.yonedaEquiv.symm x) p) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInr Δ[0] K)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInr_fatInclusion] at h
  exact h

/-- 概要：両端固定の fat join の錐の左端は指定頂点の一点の図式に定値。
方針：固定した両端の図式を左包含へ制限する。
規約：全次数での射の等式。
使われ方：Kerodon §4.6.6（Tag 04HY） の普遍族の左端の計算。 -/
lemma fixedFatConeSpace_inl {K X : SSet.{u}} (p : K ⟶ X) (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinEndpointInclusion (Δ[0] : SSet.{u}) K)).app X)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc (SSet.yonedaEquiv.symm x) p)) ≫
      (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl (Δ[0] : SSet.{u}) K)).app X =
        SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm x)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedDiagramι_pre_factor (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinEndpointInclusion (Δ[0] : SSet.{u}) K)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc (SSet.yonedaEquiv.symm x) p) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInl Δ[0] K)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInl_fatInclusion] at h
  exact h

/-- 概要：両端固定の fat join の錐から頂点の固定条件を忘れる。
方針：右端の固定条件で太い slice の fiber へ持ち上げる。
規約：関手空間における族の値を変えない。
使われ方：Kerodon §4.6.6（Tag 04HY） の既存の普遍性への接続。 -/
noncomputable def fixedFatConeToLaxSlice {K X : SSet.{u}} (p : K ⟶ X) (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedEndpointFatConeSpace p x ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxSlice p :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι
    ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinEndpointInclusion (Δ[0] : SSet.{u}) K)).app X)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc (SSet.yonedaEquiv.symm x) p))) (fixedFatConeSpace_inr p x)

/-- 概要：固定頂点の fat join の錐の族を任意パラメータの fat join 上へ展開する。
方針：太い slice への忘却射と既存の uncurry を合成する。
規約：パラメータは join の左因子。
使われ方：Kerodon §4.6.6（Tag 04HY） の相対 join 延長に入力する実際の図式。 -/
noncomputable def fixedFatConeUncurry {A K X : SSet.{u}} {p : K ⟶ X} {x : X _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedEndpointFatConeSpace p x) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A K ⟶ X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxSliceUncurry (f ≫ fixedFatConeToLaxSlice p x)

/-- 概要：展開した固定頂点の錐の右端は元の図式。
方針：太い slice の uncurry の固定条件を使う。
規約：パラメータ A は任意。
使われ方：Kerodon §4.6.6（Tag 04HY） の join 図式を curry する右端条件。 -/
lemma fixedFatConeUncurry_inr {A K X : SSet.{u}} {p : K ⟶ X} {x : X _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedEndpointFatConeSpace p x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A K ≫ fixedFatConeUncurry f = p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxSliceUncurry_fixed _

/-- 概要：展開した固定頂点の錐の左端は指定頂点に定値。
方針：左包含への制限を uncurry し、一点への唯一の射で評価する。
規約：高次のパラメータでも頂点を固定する。
使われ方：Kerodon §4.6.6（Tag 04HY） の相対 join 延長の後の固定頂点への回収。 -/
lemma fixedFatConeUncurry_inl {A K X : SSet.{u}} {p : K ⟶ X} {x : X _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedEndpointFatConeSpace p x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A K ≫ fixedFatConeUncurry f = SSet.const x := by
  have hleft : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl (Δ[0] : SSet.{u}) K ▷ A) ≫
      uncurry (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι
        ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinEndpointInclusion (Δ[0] : SSet.{u}) K)).app X)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc (SSet.yonedaEquiv.symm x) p))) =
      fst (Δ[0] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm x := by
    rw [← uncurry_pre_app, Category.assoc, fixedFatConeSpace_inl, SSet.comp_const,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]
  rw [fixedFatConeUncurry, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxSliceUncurry_inl]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxSliceLeftInput A K ≫ uncurry (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι
    ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinEndpointInclusion (Δ[0] : SSet.{u}) K)).app X)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc (SSet.yonedaEquiv.symm x) p))) = _
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxSliceLeftInput A K =
      lift (stdSimplex.isTerminalObj₀.from A) (𝟙 A) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl Δ[0] K ▷ A) := rfl
  rw [hi, Category.assoc, hleft, ← Category.assoc, lift_fst]
  rw [stdSimplex.isTerminalObj₀.hom_ext (stdSimplex.isTerminalObj₀.from A)
    (SSet.const (stdSimplex.obj₀Equiv.symm 0))]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.const_point_comp_yoneda x

/-- 概要：固定頂点の錐の展開はパラメータの前合成を保つ。
方針：太い slice の uncurry の自然性を使う。
規約：図式と頂点は共通に固定する。
使われ方：Kerodon §4.6.6（Tag 04HY） の部分族を保つ逆射の構成。 -/
lemma fixedFatConeUncurry_precomp {A B K X : SSet.{u}} {p : K ⟶ X} {x : X _⦋0⦌}
    (f : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedEndpointFatConeSpace p x) (a : A ⟶ B) :
    fixedFatConeUncurry (a ≫ f) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinMap a (𝟙 K) ≫ fixedFatConeUncurry f := by
  unfold fixedFatConeUncurry
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxSliceUncurry_precomp]

/-- 概要：固定頂点の錐の族は展開した fat join 上の射で決まる。
方針：太い slice の uncurry の単射性の後で fiber の包含の値を比較する。
規約：標的の充填性を要求しない。
使われ方：Kerodon §4.6.6（Tag 04HY） の普遍性の一意性。 -/
lemma fixedFatConeUncurry_injective {A K X : SSet.{u}} (p : K ⟶ X) (x : X _⦋0⦌) :
    Function.Injective (fixedFatConeUncurry (A := A) (p := p) (x := x)) := by
  intro f g h
  have he : f ≫ fixedFatConeToLaxSlice p x = g ≫ fixedFatConeToLaxSlice p x :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxSliceUncurry_injective h
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext
    ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinEndpointInclusion (Δ[0] : SSet.{u}) K)).app X)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc (SSet.yonedaEquiv.symm x) p))
  have hi := congrArg (fun z ↦ z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι
    ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr (Δ[0] : SSet.{u}) K)).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)) he
  exact hi

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
