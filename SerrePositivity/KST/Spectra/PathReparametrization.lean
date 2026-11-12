module

public import SerrePositivity.KST.Spectra.IntervalContraction

/-!
概要：path の区間変数を収縮する再パラメータ付け。
方針：区間と時刻に収縮を適用し、path のパラメータは保持する。
規約：直積の成分を明示して自然性と端点を検査する。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。path space の収縮。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：区間と時刻に収縮を施し、中央のパラメータを保持する。
方針：各次数で (s,p,t) を (収縮(s,t),p) に送る。
規約：P は任意の単体集合。
使われ方：Goerss–Jardine I §7。path space の評価の再パラメータ付け。 -/
def pathReparametrization (P : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u}.right ⊗ (P ⊗ (Δ[1] : SSet.{u})) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u}.right ⊗ P where
  app m := ↾fun s ↦ (intervalContractionMap.app m (s.1, s.2.2), s.2.1)
  naturality m n f := by
    apply ConcreteCategory.hom_ext
    intro s
    apply Prod.ext
    · exact congrArg (fun k :
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u}.right ⊗ (Δ[1] : SSet.{u})).obj m ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u}.right.obj n ↦
          k (s.1, s.2.2)) (intervalContractionMap.{u}.naturality f)
    · rfl

/-- 概要：再パラメータ付けの時刻一は恒等射。
方針：区間の収縮の時刻一の式を成分ごとに使う。
規約：P の成分はそのまま保持する。
使われ方：Goerss–Jardine I §7。path space の収縮の終端。 -/
theorem pathReparametrization_one (P : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u}.right ◁ (SSet.ι₁ : P ⟶ _) ≫ pathReparametrization P = 𝟙 _ := by
  apply SSet.hom_ext
  intro m
  apply ConcreteCategory.hom_ext
  intro s
  apply Prod.ext
  · exact congrArg (fun k : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u}.right ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u}.right ↦
      k.app m s.1) intervalContraction_one
  · rfl

/-- 概要：再パラメータ付けの時刻零は区間成分を基点に固定する。
方針：区間の収縮の時刻零の式を成分ごとに使う。
規約：P の成分は保持する。
使われ方：Goerss–Jardine I §7。path space の収縮の初端。 -/
theorem pathReparametrization_zero (P : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u}.right ◁ (SSet.ι₀ : P ⟶ _) ≫ pathReparametrization P =
      lift (toUnit (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u}.right ⊗ P)) (snd _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u}.right P) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u}.hom ▷ P := by
  apply SSet.hom_ext
  intro m
  apply ConcreteCategory.hom_ext
  intro s
  apply Prod.ext
  · exact congrArg (fun k : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u}.right ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u}.right ↦
      k.app m s.1) intervalContraction_zero
  · rfl

/-- 概要：区間の基点上で再パラメータ付けは基点を固定する。
方針：区間の収縮が全時刻で基点を固定する式を使う。
規約：パラメータの P 成分は保持する。
使われ方：Goerss–Jardine I §7。点つき Hom への curry の条件。 -/
theorem pathReparametrization_basepoint (P : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u}.hom ▷ (P ⊗ (Δ[1] : SSet.{u})) ≫ pathReparametrization P =
      lift (toUnit (𝟙_ SSet.{u} ⊗ (P ⊗ (Δ[1] : SSet.{u}))))
        (snd (𝟙_ SSet.{u}) (P ⊗ (Δ[1] : SSet.{u})) ≫ fst P (Δ[1] : SSet.{u})) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u}.hom ▷ P := by
  apply SSet.hom_ext
  intro m
  apply ConcreteCategory.hom_ext
  intro s
  apply Prod.ext
  · exact congrArg (fun k : (𝟙_ SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u}.right ↦
      k.app m (s.1, s.2.2)) intervalContraction_basepoint
  · rfl

/-- 概要：再パラメータ付けは P の射に自然。
方針：区間と時刻の成分を変えず、中央の成分の射を比較する。
規約：任意の単体集合の射 f。
使われ方：Goerss–Jardine I §7。定数 path の固定。 -/
@[reassoc]
theorem pathReparametrization_natural {P Q : SSet.{u}} (f : P ⟶ Q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u}.right ◁ (f ▷ (Δ[1] : SSet.{u})) ≫ pathReparametrization Q =
      pathReparametrization P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u}.right ◁ f := by
  ext m s <;> rfl

end

end SerrePositivity.KST.Spectra
