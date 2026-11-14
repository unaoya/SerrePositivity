module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# 単体集合の次数ごとの添字付き余積

概要：各次数で依存和を取って単体集合の余積を構成する。
方針：単体の作用は添字を保ち、各成分の作用だけを使う。余積の普遍性も明示する。
規約：Segal 1974 Lemma 1.8 の telescope の偶数・奇数段の余積に使う。
使われ方：余積の引き戻しと Kan 条件を、添字と成分に分けて証明する。
-/

@[expose] public section
universe u v
namespace SerrePositivity.KST.Comparison
end SerrePositivity.KST.Comparison
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.Comparison
open CategoryTheory Limits
open scoped ConcreteCategory
variable {ι : Type v}

/--
概要：単体集合の族の次数ごとの依存和。
方針：単体の作用で依存和の添字を固定する。
規約：対象の universe は添字と値の universe の最大。
使われ方：telescope の頂点と辺の余積。
-/
def simplicialSum (A : ι → SSet.{max u v}) : SSet.{max u v} where
  obj d := Σ i, (A i).obj d
  map θ := ↾fun x => ⟨x.1, (A x.1).map θ x.2⟩
  map_id d := by
    apply ConcreteCategory.hom_ext
    intro x
    change Sigma.mk x.1 ((A x.1).map (𝟙 d) x.2) = x
    simp
  map_comp {X Y Z} θ φ := by
    apply ConcreteCategory.hom_ext
    intro x
    change Sigma.mk x.1 ((A x.1).map (θ ≫ φ) x.2) =
      (⟨x.1, (A x.1).map φ ((A x.1).map θ x.2)⟩ : Σ i, (A i).obj Z)
    simp

/--
概要：添字付き余積への成分の包含。
方針：依存和の構成子を各次数で使う。
規約：添字を固定した自然変換。
使われ方：余積の普遍性と telescope の各段階の写像。
-/
def simplicialSumInclusion (A : ι → SSet.{max u v}) (i : ι) : A i ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSum A where
  app _ := ↾fun x => ⟨i, x⟩

/--
概要：添字付き余積からの射。
方針：各成分の射を依存和の元へ適用する。
規約：始域の添字を終域へは持ち越さない。
使われ方：余積の普遍性と telescope の脚。
-/
def simplicialSumDesc {A : ι → SSet.{max u v}} {B : SSet.{max u v}}
    (f : ∀ i, A i ⟶ B) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSum A ⟶ B where
  app d := ↾fun x => (f x.1).app d x.2
  naturality _ _ θ := by
    ext x
    exact congrArg (fun t => t x.2) ((f x.1).naturality θ)

/--
概要：成分の包含と余積からの射の合成は指定した成分の射である。
方針：次数ごとの定義を計算する。
規約：指定した余錐の可換性。
使われ方：余積の普遍性。
-/
@[simp] theorem simplicialSumInclusion_desc {A : ι → SSet.{max u v}} {B : SSet.{max u v}}
    (f : ∀ i, A i ⟶ B) (i : ι) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion A i ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumDesc f = f i := rfl

/--
概要：添字付き余積からの射は各成分への制限で決まる。
方針：次数ごとの元を添字と成分に分解する。
規約：成分ごとの等式から自然変換の等式を得る。
使われ方：余積の写像の恒等・合成と自然性。
-/
theorem simplicialSum_hom_ext {A : ι → SSet.{max u v}} {B : SSet.{max u v}}
    {f g : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSum A ⟶ B}
    (h : ∀ i, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion A i ≫ f = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion A i ≫ g) : f = g := by
  apply NatTrans.ext
  funext d
  ext x
  exact congrArg (fun t => t.app d x.2) (h x.1)

/--
概要：次数ごとの依存和は実際に余積である。
方針：成分ごとの射の desc と、その計算・一意性を普遍性へまとめる。
規約：抽象的な余積の選択に依存しない余錐。
使われ方：局所化同型の余積保存をこの模型へ移す。
-/
def simplicialSumIsCoproduct (A : ι → SSet.{max u v}) :
    IsColimit (Cofan.mk (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSum A) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion A)) :=
  Cofan.IsColimit.mk _ (fun s => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumDesc s.inj)
    (fun _ _ => rfl) (fun _ _ h => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSum_hom_ext (fun i => h i))

/--
概要：成分ごとの射から添字を保つ余積の射を作る。
方針：各成分の射の後で同じ添字の包含を合成する。
規約：始域と終域は同じ添字型を持つ。
使われ方：自然変換の各段階を余積にまとめる。
-/
def simplicialSumMap {A B : ι → SSet.{max u v}} (f : ∀ i, A i ⟶ B i) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSum A ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSum B :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumDesc (fun i => f i ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion B i)

/--
概要：余積の射は各包含と可換である。
方針：desc の成分の計算を使う。
規約：添字を変えない自然性の式。
使われ方：図式の余積の可換性。
-/
@[simp] theorem simplicialSumInclusion_map {A B : ι → SSet.{max u v}}
    (f : ∀ i, A i ⟶ B i) (i : ι) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion A i ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumMap f =
      f i ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion B i := rfl

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSum (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.simplicialSum := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSum

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumDesc (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.simplicialSumDesc := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumDesc

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.simplicialSumInclusion := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.simplicialSumInclusion_desc := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion_desc

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.simplicialSumInclusion_map := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion_map

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumIsCoproduct (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.simplicialSumIsCoproduct := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumIsCoproduct

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumMap (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.simplicialSumMap := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumMap

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.simplicialSum_hom_ext := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSum_hom_ext

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.simplicialSum._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSum._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.simplicialSum._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSum._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.simplicialSumDesc._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumDesc._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.simplicialSumInclusion._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.simplicialSumIsCoproduct._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumIsCoproduct._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.simplicialSumIsCoproduct._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumIsCoproduct._proof_2
