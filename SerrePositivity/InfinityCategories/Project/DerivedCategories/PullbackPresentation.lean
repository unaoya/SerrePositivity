module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.InfinityCategory
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeLimits
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.PullbackFiberComparison

/-! # Semifree 四角形の標準 fiber 表示

概要：D(S) の四角形から標準 cospan と semifree な fiber を取り出す。
方針：充満包含の下で通常の鎖写像を取り出し、各頂点の semifree 性を用いる。
規約：任意の四角形に定義する。使われ方：D4 の比較射。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S]

/-- 概要：D(S) から全複体の dg nerve への包含。
方針：充満 dg 包含の nerve を取る。
規約：複体の元は変えない。使われ方：四角形の鎖写像表示。 -/
abbrev derivedInfinityInclusion : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion S (Complex S) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S))

/-- 概要：D(S) の四角形の cospan を通常の鎖写像で表示する。
方針：全複体への包含後の標準表示を用いる。
規約：左・右・共通の終域を一意の式で取り出す。使われ方：標準 fiber の定義。 -/
abbrev derivedSquarePresentation
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ComplexCospanPresentation (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (F ≫ derivedInfinityInclusion)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.squareCospanPresentation (F ≫ derivedInfinityInclusion)

/-- 概要：抽出した cospan の左対象は semifree である。
方針：元の D(S) の辺の始頂点の所属を使う。
規約：四角形の極限性は不要。使われ方：fiber の閉性の入力。 -/
lemma derivedSquarePresentation_left
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S (derivedSquarePresentation F).leftObj := by
  let s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) 1 := SSet.yonedaEquiv (SSet.horn₂₂.ι₀₂ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan F)
  exact (s.obj 0).property

/-- 概要：抽出した cospan の右対象は semifree である。
方針：もう一方の辺の始頂点の所属を使う。
規約：四角形は任意。使われ方：fiber の閉性の入力。 -/
lemma derivedSquarePresentation_right
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S (derivedSquarePresentation F).rightObj := by
  let s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) 1 := SSet.yonedaEquiv (SSet.horn₂₂.ι₁₂ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan F)
  exact (s.obj 0).property

/-- 概要：抽出した cospan の終域は semifree である。
方針：左の辺の終頂点の所属を使う。
規約：四角形は任意。使われ方：fiber の閉性の入力。 -/
lemma derivedSquarePresentation_target
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S (derivedSquarePresentation F).targetObj := by
  let s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) 1 := SSet.yonedaEquiv (SSet.horn₂₂.ι₀₂ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan F)
  exact (s.obj 1).property

/-- 概要：四角形から抽出した標準 fiber は semifree である。
方針：三頂点の所属と有限直和・fiber の閉性を合成する。
規約：標準 fiber は二射の差の mapping cone の −1 シフト。使われ方：D4 の比較先。 -/
def derivedSquareStandardFiber
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackFiber (derivedSquarePresentation F).leftMap (derivedSquarePresentation F).rightMap,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_biprodFiber S (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberDifference _ _)
      (derivedSquarePresentation_left F) (derivedSquarePresentation_right F)
      (derivedSquarePresentation_target F)⟩

/-- 概要：抽出した cospan の標準 fiber 四角形を D(S) 内で構成する。
方針：N7d の semifree 四角形を三頂点の所属証明で具体化する。
規約：元の四角形の極限性を仮定しない。使われ方：同じ図式上の標準極限錐。 -/
def derivedSquareFiberSquare
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) :
    (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFiberSquare (derivedSquarePresentation F).leftMap (derivedSquarePresentation F).rightMap
    (derivedSquarePresentation_left F) (derivedSquarePresentation_right F)
    (derivedSquarePresentation_target F)

/-- 概要：標準 fiber 四角形は D(S) の引き戻し四角形である。
方針：N7d の標準引き戻し定理を用いる。
規約：任意の可換環。使われ方：比較先の極限性。 -/
lemma derivedSquareFiberSquare_isPullback
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (derivedSquareFiberSquare F) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFiberSquare_isPullback _ _ _ _ _

/-- 概要：標準 fiber 四角形と元の四角形の cospan は一致する。
方針：充満包含の単射性で全複体へ移し、抽出した標準表示の等式を使う。
規約：追加の整合性条件は不要。使われ方：同じ slice 内の二つの錐の比較。 -/
lemma derivedSquareFiberSquare_cospan
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (derivedSquareFiberSquare F) = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan F := by
  apply (cancel_mono (derivedInfinityInclusion (S := S))).1
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (derivedSquareFiberSquare F ≫ derivedInfinityInclusion) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (F ≫ derivedInfinityInclusion)
  rw [derivedSquareFiberSquare, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFiberSquare_inclusion]
  exact (derivedSquarePresentation F).cospan_eq

/-- 概要：標準四角形の錐の頂点は抽出した fiber の頂点である。
方針：包含による単射性と全複体の標準錐の頂点公式を使う。
規約：対象の semifree 証明は証明の一意性で無関係。使われ方：比較射の終域の同定。 -/
lemma derivedSquareFiberSquare_vertex
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (derivedSquareFiberSquare F)).vertex =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (derivedSquareStandardFiber F) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.map_inclusion_injective S (Complex S) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S) 0)
  have he := congrArg (fun q => (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone q).vertex)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFiberSquare_inclusion (derivedSquarePresentation F).leftMap
      (derivedSquarePresentation F).rightMap (derivedSquarePresentation_left F)
      (derivedSquarePresentation_right F) (derivedSquarePresentation_target F))
  exact he.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone_vertex _ _)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
