module
public import SerrePositivity.KST.SConstruction.Cofinality.RelativeFlags
public import SerrePositivity.KST.SConstruction.Cofinality.StageDetection
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberLocalizingEdges
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ContinuousKanFilling

/-!
概要：Sp-7 の一般供給を仮定引数として元の全多次数の相対旗へ代入する。
方針：標準模型での供給仕様をデータに束ね、反復 S の実完備化証拠を渡す。
規約：供給の存在を公理化せず、離散性から実現比較を直接推論しない。
使われ方：一般 API の到着前にも型を固定して進める相対 S• の入口。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet Spectra
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：指定完全射の wide 部分複体と亜群化の離散性の供給仕様。
方針：全単体条件を明記して Sp-7 の結論を標準模型へ制限する。
規約：この構造の存在は仮定引数からだけ取得する。
使われ方：同じ反復 S 射に代入される供給値。 -/
structure WideStageData {X Y : StableModel.{u}} (f : X ⟶ Y) where
  subcomplex : Y.carrier.Subcomplex
  simplex_spec : ∀ (n : ℕ) (s : Y.carrier _⦋n⦌),
    s ∈ subcomplex.obj (Opposite.op ⦋n⦌) ↔ ∀ θ : ⦋1⦌ ⟶ ⦋n⦌,
      Y.carrier.map θ.op s ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges
        {y | ∃ x : X.carrier _⦋0⦌, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (f.val.app (Opposite.op ⦋0⦌) x) y)}
  quasicategory : Quasicategory (subcomplex : SSet.{u})
  discrete : ∀ (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (subcomplex : SSet.{u})) _⦋0⦌)
    (n : ℕ), 0 < n →
      Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (subcomplex : SSet.{u})) n x)

/-- 概要：Sp-7 の供給を標準模型の指定完備化射で消費する仮定型。
方針：一般 API の安定単体集合の引数へ各標準模型の carrier を渡せる形にする。
規約：証明は宣言せず、各利用定理の明示的な引数に取る。
使われ方：到着前の相対図式の組立と到着後の代入。 -/
def StableWideCofinalitySupply : Prop :=
  ∀ (X Y : StableModel.{u}) (f : X ⟶ Y),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val → Nonempty (WideStageData f)

/-- 概要：一般の Sp-7 の結論を標準模型の供給引数へ変換する。
方針：安定 carrier と完全射の instance を渡し、存在証明を構造に束ねる。
規約：新しい一般定理を仮定せず、呼出側から渡された証明だけを使用する。
使われ方：Sp-7 の公開名の到着時の一回の代入。 -/
theorem stableWideCofinalitySupply_of_api
    (api : ∀ (C D : SSet.{u}) [Quasicategory C] [Quasicategory D]
      [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable D] (f : C ⟶ D) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor f],
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f →
      ∃ M : D.Subcomplex,
        (∀ (n : ℕ) (s : D _⦋n⦌), s ∈ M.obj (Opposite.op ⦋n⦌) ↔
          ∀ θ : ⦋1⦌ ⟶ ⦋n⦌, D.map θ.op s ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges
            {y | ∃ x : C _⦋0⦌, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (f.app (Opposite.op ⦋0⦌) x) y)}) ∧
        Quasicategory (M : SSet.{u}) ∧
        ∀ (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (M : SSet.{u})) _⦋0⦌) (n : ℕ),
          0 < n → Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (M : SSet.{u})) n x)) :
    StableWideCofinalitySupply.{u} := by
  intro X Y f hf
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor f.val := stableModelHom_exact f
  obtain ⟨M, hs, hq, hd⟩ := api X.carrier Y.carrier f.val hf
  exact ⟨⟨M, hs, hq, hd⟩⟩

/-- 概要：同じ全多次数の実完備化射に一般供給を代入する。
方針：反復 S の完備化保存を使い、その射の供給値を一つ選ぶ。
規約：異なる多次数で独立に選んだ値の自然性は別途全単体条件で検査する。
使われ方：相対旗の各多次数の wide 部分複体。 -/
def multiWideStageData (supply : StableWideCofinalitySupply.{u})
    (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}}
    (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    WideStageData (((multiSEndofunctor r).obj ι).map f) :=
  Classical.choice (supply _ _ _ (multiSEndofunctor_map_isIdempotentCompletion r ι f hf))

/-- 概要：供給された wide 部分圏の相対旗を元の反復 S の多次数に構成する。
方針：その全旗を頂点とする ambient 全部分圏を取る。
規約：wide 内部 Hom を相対旗の全射に流用しない。
使われ方：相対 S• の実現前の各段。 -/
def suppliedMultiRelativeFlags (supply : StableWideCofinalitySupply.{u})
    (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}}
    (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (K : SSet.{u}) :
    SSet.{u} :=
  multiRelativeFlags r ι Y (multiWideStageData supply r ι f hf).subcomplex K

/-- 概要：供給値から構成した相対旗は quasicategory。
方針：同じ反復 S の関手圏の全部分複体の instance を使う。
規約：供給型の不透明な略記を class 探索で展開することに依存しない。
使われ方：相対旗内の頂点同型の反映と全部分圏の構成。 -/
instance suppliedMultiRelativeFlags_quasicategory (supply : StableWideCofinalitySupply.{u})
    (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}}
    (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (K : SSet.{u}) :
    Quasicategory (suppliedMultiRelativeFlags supply r ι f hf K) :=
  multiRelativeFlags_quasicategory r ι Y (multiWideStageData supply r ι f hf).subcomplex K

/-- 概要：同じ多次数の供給値の亜群化は全頂点で正次数が自明。
方針：一般供給の証明フィールドをそのまま使う。
規約：相対旗の実現の離散性とはまだ同一視しない。
使われ方：相対実現比較へ渡す離散性の証拠。 -/
theorem multiWideStageData_discrete (supply : StableWideCofinalitySupply.{u})
    (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}}
    (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj
      ((multiWideStageData supply r ι f hf).subcomplex : SSet.{u})) _⦋0⦌)
    (n : ℕ) (hn : 0 < n) :
    Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj
      ((multiWideStageData supply r ι f hf).subcomplex : SSet.{u})) n x) :=
  (multiWideStageData supply r ι f hf).discrete x n hn

end SerrePositivity.KST.SConstruction.Cofinality
