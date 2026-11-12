module
public import SerrePositivity.KST.SConstruction.SPathBoundary
public import SerrePositivity.KST.SConstruction.CoreTrivialFibration
public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalLocalizedEquivalence

/-! # S の経路構成の第一行の自然な比較
概要：先頭を保つ単体作用素の下で第一行制限を自然変換へ束ねる。
方針：先頭追加した順序写像と正の端点の包含の可換性を計算する。
規約：各段は元の第一行制限。使われ方：経路構成の fiber 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open scoped Simplicial

/-- 概要：元の単体作用素が正の端点の添字に作用する順序写像。
方針：有限順序集合の射を宇宙持ち上げへ移す。
規約：先頭追加前の単体を添字とする。使われ方：経路の第一行の作用素。 -/
def pathFirstRowOrderMap {d e : SimplexCategory} (f : d ⟶ e) :
    ULift.{u} (Fin (d.len + 1)) →o ULift.{u} (Fin (e.len + 1)) where
  toFun j := ⟨f.toOrderHom j.down⟩
  monotone' _a _b h := f.toOrderHom.monotone h

/-- 概要：経路の正の端点の nerve を全単体作用素について関手化する。
方針：端点の順序写像を nerve へ送る。
規約：第 n 段は n+1 個の端点。使われ方：第一行の関手図式の始域。 -/
def pathFirstRowNerveFunctor : SimplexCategory ⥤ SSet.{u} where
  obj d := firstRowNerve (d.len + 1)
  map f := nerveMap (pathFirstRowOrderMap f).toFunctor
  map_id _ := rfl
  map_comp _ _ := rfl

/-- 概要：経路の正の端点の nerve は標準単体の関手と自然に同型。
方針：各次数の標準単体と有限順序圏の nerve の同型を使う。
規約：全単体作用素について厳密に自然。使われ方：Fun(Δ[n],C) 表示との照合。 -/
def pathFirstRowSimplexNatIso : stdSimplex.{u} ≅ pathFirstRowNerveFunctor :=
  NatIso.ofComponents (fun d => firstRowSimplexIso d.len) (by
    intro d e f
    rfl)

/-- 概要：第一行の包含は先頭追加した単体作用素について自然。
方針：端点 j は両経路で (0,(f j)+1) に写ることを使う。
規約：nerve の射の厳密等号。使われ方：経路の第一行制限の自然性。 -/
lemma pathFirstRowInclusion_naturality {d e : SimplexCategory} (f : d ⟶ e) :
    firstRowInclusion.{u} (d.len + 1) ≫
        arNerveMap (SimplexPrefix.functor.map f).toOrderHom =
      pathFirstRowNerveFunctor.map f ≫ firstRowInclusion (e.len + 1) := rfl

/-- 概要：経路の第一行に相当する関手 quasicategory の単体的図式。
方針：正の端点の nerve の写像による前合成を使う。
規約：全ての単体作用素を含む。使われ方：経路 S からの自然な第一行比較の標的。 -/
def pathFirstRowDiagram (C : SSet.{u}) : SimplicialObject SSet.{u} where
  obj d := (ihom (pathFirstRowNerveFunctor.obj d.unop)).obj C
  map f := (pre (pathFirstRowNerveFunctor.map f.unop)).app C
  map_id d := by
    rw [unop_id, pathFirstRowNerveFunctor.map_id, pre_id]
    rfl
  map_comp f g := by
    rw [unop_comp, pathFirstRowNerveFunctor.map_comp, pre_map, NatTrans.comp_app]

/-- 概要：経路の第一行の各段の関手空間は quasicategory。
方針：内部 Hom の quasicategory 性。
規約：C が quasicategory で足りる。使われ方：core の比較の入力。 -/
instance pathFirstRowDiagram_obj_quasicategory (C : SSet.{u}) [Quasicategory C]
    (d : SimplexCategoryᵒᵖ) : Quasicategory ((pathFirstRowDiagram C).obj d) := by
  change Quasicategory ((ihom (firstRowNerve (d.unop.len + 1))).obj C)
  infer_instance

/-- 概要：S の経路構成から全第一行の関手空間への自然変換。
方針：元の第一行制限と、先頭を保つ添字の可換性を使う。
規約：各段の元の gapped 図式を保持する。使われ方：経路と第一行の単体的比較。 -/
def pathFirstRowRestriction (C : SSet.{u}) :
    simplicialPath (simplicialSConstruction C) ⟶ pathFirstRowDiagram C where
  app d := firstRowRestriction (d.unop.len + 1) C
  naturality {d e} f := by
    change sMap C (SimplexPrefix.functor.map f.unop).toOrderHom ≫
        ((gappedSubcomplex (e.unop.len + 1) C).ι ≫
          (pre (firstRowInclusion (e.unop.len + 1))).app C) =
      ((gappedSubcomplex (d.unop.len + 1) C).ι ≫
        (pre (firstRowInclusion (d.unop.len + 1))).app C) ≫
          (pre (pathFirstRowNerveFunctor.map f.unop)).app C
    rw [← Category.assoc]
    rw [sMap_ι (m := e.unop.len + 1) (n := d.unop.len + 1) C
      (SimplexPrefix.functor.map f.unop).toOrderHom]
    rw [Category.assoc, Category.assoc]
    rw [← NatTrans.comp_app, ← pre_map, ← NatTrans.comp_app, ← pre_map,
      pathFirstRowInclusion_naturality]

/-- 概要：経路の第一行制限は各段で trivial Kan fibration。
方針：既証の全 gapped 図式の第一行制限の定理を使う。
規約：C は安定な quasicategory。使われ方：経路の core の比較。 -/
instance pathFirstRowRestriction_trivialKanFibration (C : SSet.{u})
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] (d : SimplexCategoryᵒᵖ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((pathFirstRowRestriction C).app d) :=
  firstRowRestriction_trivialKanFibration _ C

/-- 概要：経路の第一行制限の core による自然な比較。
方針：第一行の自然変換に core 関手を後合成する。
規約：源は既存の core S の経路構成。使われ方：対角実現の比較。 -/
def corePathFirstRowRestriction (C : SSet.{u}) :
    simplicialPath (simplicialCoreSConstruction C) ⟶
      pathFirstRowDiagram C ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor :=
  Functor.whiskerRight (pathFirstRowRestriction C) _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor

/-- 概要：core の経路の第一行制限も各段で trivial Kan fibration。
方針：quasicategory 間の自明ファイブレーションの core への制限を使う。
規約：追加の存在仮定なし。使われ方：対角の弱同値。 -/
instance corePathFirstRowRestriction_trivialKanFibration (C : SSet.{u})
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] (d : SimplexCategoryᵒᵖ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((corePathFirstRowRestriction C).app d) := by
  let : Quasicategory ((simplicialPath (simplicialSConstruction C)).obj d) := by
    change Quasicategory (sConstruction (d.unop.len + 1) C)
    infer_instance
  exact coreMap_trivialKanFibration ((pathFirstRowRestriction C).app d)

/-- 概要：S の経路実現から第一行の関手空間の core の対角への射。
方針：自然な core 比較を対角関手で写す。
規約：対角の Kan 性は仮定しない。使われ方：経路の fiber 比較の実現模型。 -/
def pathFirstRowDiagonalComparison (C : SSet.{u}) : sPathRealization C ⟶
    simplicialDiagonalFunctor.obj (pathFirstRowDiagram C ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor) :=
  simplicialDiagonalFunctor.map (corePathFirstRowRestriction C)

/-- 概要：経路の第一行比較は対角実現後に anodyne 局所化で可逆。
方針：各段の core の自明ファイブレーションを対角比較の定理へ渡す。
規約：元の対角の Kan 性は不要。使われ方：経路の自然な弱同値。 -/
lemma pathFirstRowDiagonalComparison_localized_isIso (C : SSet.{u})
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] :
    IsIso (AnodyneHomotopy.anodyneQ.map (pathFirstRowDiagonalComparison C)) := by
  have hi (d : SimplexCategoryᵒᵖ) :
      IsIso (AnodyneHomotopy.anodyneQ.map ((corePathFirstRowRestriction C).app d)) :=
    map_isIso_of_trivialKanFibration AnodyneHomotopy.anodyneQ
      (Localization.inverts AnodyneHomotopy.anodyneQ anodyneExtensions) _
  exact SerrePositivity.BisimplicialModel.localized_diagonal_map (corePathFirstRowRestriction C) hi

end SerrePositivity.KST.SConstruction
