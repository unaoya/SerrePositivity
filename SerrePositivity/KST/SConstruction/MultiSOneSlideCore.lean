module
public import SerrePositivity.KST.SConstruction.MultiFixedSInterchangeNaturality
public import SerrePositivity.KST.SConstruction.FixedSRealizationSwap

/-! # 全多次数での元の S₁ 内外交換の core 比較
概要：入力 S₁ の反復 core と元の最外側 S₁ の反復 core を自然同型で比較する。
方針：完全関手の交換同型を core へ写し、元の多方向作用との厳密な式を使う。
規約：対角上では既存の実現同型を回収する。使われ方：源の零境界の厳密な比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 元の最外側 S₁ の多方向作用は、残りの反復作用への S₁ の後合成。 -/
lemma multiCoreSOne_map (r : ℕ) (X : StableModel.{u})
    {d e : Fin r → SimplexCategoryᵒᵖ} (f : d ⟶ e) :
    (multiCoreSConstruction (r + 1) X).map ((oneDirectionIndex r).map f) =
      (stableModelForget.{u} ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor).map
        ((sEndofunctor 1).map (((multiSEndofunctor r).map f).app X)) := by
  let H := stableModelForget.{u} ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor
  have h : ((multiSEndofunctor (r + 1)).map ((oneDirectionIndex r).map f)).app X =
      (sEndofunctor 1).map (((multiSEndofunctor r).map f).app X) := by
    change ((simplicialStableEndofunctor.map (𝟙 (Opposite.op ⦋1⦌))).app
      (((multiSEndofunctor r).obj d).obj X) ≫
        (sEndofunctor 1).map (((multiSEndofunctor r).map f).app X)) = _
    rw [CategoryTheory.Functor.map_id]
    simp only [NatTrans.id_app, Category.id_comp]
  exact congrArg H.map h

/-- 任意の多次数における元の core 図式の S₁ 内外交換。 -/
def multiSOneSlideCoreAt (r : ℕ) (X : StableModel.{u})
    (d : Fin r → SimplexCategoryᵒᵖ) :
    (multiCoreSConstruction r (sStableModel 1 X)).obj d ≅
      (multiCoreSConstruction (r + 1) X).obj ((oneDirectionIndex r).obj d) := by
  let H := stableModelForget.{u} ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor
  change H.obj (((multiSEndofunctor r).obj d).obj (sStableModel 1 X)) ≅
    H.obj (sStableModel 1 (((multiSEndofunctor r).obj d).obj X))
  exact H.mapIso ((multiFixedSEndofunctorIso 1 r d).app X)

/-- 多次数 core 交換の順射は元の完全関手の交換の core 像。 -/
lemma multiSOneSlideCoreAt_hom (r : ℕ) (X : StableModel.{u})
    (d : Fin r → SimplexCategoryᵒᵖ) :
    (multiSOneSlideCoreAt r X d).hom =
      (stableModelForget.{u} ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor).map
        ((multiFixedSEndofunctorIso 1 r d).hom.app X) := rfl

/-- 元の core 交換の成分は全多次数の射について自然。 -/
lemma multiSOneSlideCoreAt_naturality (r : ℕ) (X : StableModel.{u})
    {d e : Fin r → SimplexCategoryᵒᵖ} (f : d ⟶ e) :
    (multiCoreSConstruction r (sStableModel 1 X)).map f ≫
      (multiSOneSlideCoreAt r X e).hom =
      (multiSOneSlideCoreAt r X d).hom ≫
        (multiCoreSConstruction (r + 1) X).map ((oneDirectionIndex r).map f) := by
  rw [multiSOneSlideCoreAt_hom, multiSOneSlideCoreAt_hom]
  let H := stableModelForget.{u} ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor
  change H.map (((multiSEndofunctor r).map f).app (sStableModel 1 X)) ≫
    H.map ((multiFixedSEndofunctorIso 1 r e).hom.app X) =
    H.map ((multiFixedSEndofunctorIso 1 r d).hom.app X) ≫
      (multiCoreSConstruction (r + 1) X).map ((oneDirectionIndex r).map f)
  rw [multiCoreSOne_map, ← H.map_comp, ← H.map_comp]
  exact congrArg H.map (multiFixedSEndofunctorIso_naturality 1 r f X)

/-- 入力 S₁ と最外側の S₁ の全多次数 core の自然同型。 -/
def multiSOneSlideCoreIso (r : ℕ) (X : StableModel.{u}) :
    multiCoreSConstruction r (sStableModel 1 X) ≅
      oneDirectionIndex r ⋙ multiCoreSConstruction (r + 1) X :=
  NatIso.ofComponents
    (F := multiCoreSConstruction r (sStableModel 1 X))
    (G := oneDirectionIndex r ⋙ multiCoreSConstruction (r + 1) X)
    (fun (d : Fin r → SimplexCategoryᵒᵖ) => multiSOneSlideCoreAt r X d)
    (fun f => multiSOneSlideCoreAt_naturality r X f)

/-- 全多次数 core の交換の対角実現は、既存の元の S₁ 内外実現同型そのもの。 -/
lemma multiSOneSlideCoreIso_realization (r : ℕ) (X : StableModel.{u}) :
    simplicialDiagonalFunctor.map
      (Functor.whiskerLeft (multiIndexDiagonal r) (multiSOneSlideCoreIso r X).hom) =
        (sOneInnerOuterRealizationIso r X).hom := by
  apply NatTrans.ext
  funext d
  change ((stableModelForget.{u} ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor).map
    ((multiFixedSEndofunctorIso 1 r (fun _ => d)).hom.app X)).app d = _
  rw [multiFixedSEndofunctorIso_diagonal_app]
  rfl

end SerrePositivity.KST.SConstruction
