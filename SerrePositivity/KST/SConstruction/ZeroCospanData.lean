module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CospanFamilies
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroSourceArrows
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.SuspensionDiagramArrows
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathIso

/-! # 零頂点から出る脚を持つ cospan のデータ
概要：第一辺と、零対象からその終点への第二辺を引き戻しで束ねる。
方針：零対象から出る辺の終点射影を第一辺の終点で引き戻す。
規約：第一辺は 0→2、零脚は 1→2。使われ方：BGT Lemma 7.3 の固定零射の補完。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：共通終点を持つ第一辺と零対象からの辺のデータ。
方針：二つの終点評価の引き戻し。
規約：零対象と零射を選択せず全て保持する。使われ方：固定第一辺上の可縮な選択空間。 -/
def zeroCospanData (C : SSet.{u}) : SSet.{u} :=
  pullback (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourceArrowTarget C)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))

/-- 概要：零脚つき cospan のデータから第一辺を取る。
方針：引き戻しの第二射影。
規約：全次数で自然。使われ方：第一辺を固定した比較。 -/
def zeroCospanDataProjection (C : SSet.{u}) : zeroCospanData C ⟶ (ihom (Δ[1] : SSet.{u})).obj C :=
  pullback.snd _ _

/-- 概要：零脚の全選択の射影は trivial Kan fibration。
方針：零対象からの辺の終点射影の trivial Kan fibration を引き戻す。
規約：零対象の存在だけが必要。使われ方：固定第一辺上の同型の構成。 -/
instance zeroCospanDataProjection_trivialKanFibration (C : SSet.{u}) [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (zeroCospanDataProjection C) := by
  dsimp only [zeroCospanDataProjection]
  infer_instance

/-- 概要：零脚のデータを実際の cospan の関手の族に貼り合わせる。
方針：引き戻しの終点の等号で二本の辺の族を貼る。
規約：全てのパラメーターに自然。使われ方：データの同型を cospan 全体の同型にする。 -/
def zeroCospanDataDiagram (C : SSet.{u}) :
    zeroCospanData C ⟶ (ihom (horn 2 2 : SSet.{u})).obj C :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_cospanFamilyOfArrows (zeroCospanDataProjection C)
    (pullback.fst (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourceArrowTarget C)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroSourceArrow).ι)
    (by simpa only [zeroCospanDataProjection, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourceArrowTarget, Category.assoc] using
      (pullback.condition (f := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourceArrowTarget C)
        (g := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))).symm)

/-- 概要：貼り合わせた cospan の第一辺は指定データの第一辺。
方針：二辺の貼り合わせの制限式を使う。
規約：厳密等号。使われ方：固定入力の比較。 -/
lemma zeroCospanDataDiagram_left (C : SSet.{u}) :
    zeroCospanDataDiagram C ≫ (pre horn₂₂.ι₀₂).app C = zeroCospanDataProjection C :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_cospanFamilyOfArrows_left _ _ _

/-- 概要：貼り合わせた cospan の第二辺は指定された零脚。
方針：二辺の貼り合わせの制限式を使う。
規約：厳密等号。使われ方：零脚の回収。 -/
lemma zeroCospanDataDiagram_right (C : SSet.{u}) :
    zeroCospanDataDiagram C ≫ (pre horn₂₂.ι₁₂).app C =
      pullback.fst (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourceArrowTarget C)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroSourceArrow).ι :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_cospanFamilyOfArrows_right _ _ _

/-- 概要：cospan の両脚の終点評価は厳密に一致する。
方針：前合成後の評価を共通頂点の評価に直す。
規約：C は任意。使われ方：実際の cospan をデータの引き戻しへ持ち上げる。 -/
lemma zeroCospan_targets (C : SSet.{u}) :
    (pre horn₂₂.ι₀₂).app C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      (pre horn₂₂.ι₁₂).app C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt]
  congr 1

/-- 概要：零脚を持つ実際の cospan の族は零脚データへ厳密に持ち上がる。
方針：第二辺を零対象からの辺の全部分複体へ持ち上げ、第一辺と引き戻しへ合わせる。
規約：C やパラメーター A に quasicategory 性は要求しない。
使われ方：指定された零射を変更せずに cofiber の選択空間へ入れる。 -/
def zeroCospanDataLift {A C : SSet.{u}} (p : A ⟶ (ihom (horn 2 2 : SSet.{u})).obj C)
    (hp : ∀ v : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroSourceArrow
      (((pre horn₂₂.ι₁₂).app C).app (Opposite.op ⦋0⦌) (p.app (Opposite.op ⦋0⦌) v))) :
    A ⟶ zeroCospanData C :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroSourceArrow (p ≫ (pre horn₂₂.ι₁₂).app C) hp)
    (p ≫ (pre horn₂₂.ι₀₂).app C) (by
      rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourceArrowTarget, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι]
      simp only [Category.assoc]
      rw [← zeroCospan_targets])

/-- 概要：cospan の族のデータへの持ち上げは第一辺を厳密に回収する。
方針：引き戻しの第二射影。
規約：全次数での等号。使われ方：同じ第一辺の二つのデータの比較。 -/
lemma zeroCospanDataLift_projection {A C : SSet.{u}}
    (p : A ⟶ (ihom (horn 2 2 : SSet.{u})).obj C) (hp) :
    zeroCospanDataLift p hp ≫ zeroCospanDataProjection C = p ≫ (pre horn₂₂.ι₀₂).app C :=
  pullback.lift_snd _ _ _

/-- 概要：データへ持ち上げて貼り合わせると、元の cospan の族に厳密に戻る。
方針：二辺への制限で等号を確認する。
規約：頂点だけでなく全単体の等号。使われ方：cospan の同型の元の図式との照合。 -/
lemma zeroCospanDataLift_diagram {A C : SSet.{u}}
    (p : A ⟶ (ihom (horn 2 2 : SSet.{u})).obj C) (hp) :
    zeroCospanDataLift p hp ≫ zeroCospanDataDiagram C = p := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_cospanFamily_hom_ext
  · rw [Category.assoc, zeroCospanDataDiagram_left, zeroCospanDataLift_projection]
  · rw [Category.assoc, zeroCospanDataDiagram_right, ← Category.assoc]
    change ((zeroCospanDataLift p hp) ≫ pullback.fst _ _) ≫ _ = _
    rw [zeroCospanDataLift, pullback.lift_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι]

end SerrePositivity.KST.SConstruction
