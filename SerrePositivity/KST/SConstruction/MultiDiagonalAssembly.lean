module
public import SerrePositivity.KST.SConstruction.MultiSOneComparison
public import SerrePositivity.KST.SConstruction.BoundaryReduction
public import SerrePositivity.KST.SConstruction.DiagonalAssembly

/-! # 反復 S の一次方向の区間から対角への組み立て
概要：外側の一次方向を区間に沿って動かし、全反復の対角へ写す。
方針：最初の座標に α:[n]→[1]、残りに恒等射を入れる。
規約：源は一次方向を固定した実現。使われ方：反復間の構造写像の cylinder。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open scoped Simplicial

/-- 概要：一次方向を単体 α に沿って対角次数へ送る添字の射。
方針：外側には α の反対、残りには恒等射を置く。
規約：最初の S が外側。使われ方：反復の組み立て。 -/
def oneDirectionAssemblyIndex (r : ℕ) (d : SimplexCategoryᵒᵖ) (α : d.unop ⟶ ⦋1⦌) :
    (oneDirectionIndex r).obj ((multiIndexDiagonal r).obj d) ⟶
      (multiIndexDiagonal (r + 1)).obj d :=
  fun i => Fin.cases α.op (fun _ => 𝟙 d) i

/-- 概要：組み立ての添字は対角の単体作用と可換。
方針：先頭で α の前合成、残りで恒等射の合成を比較する。
規約：全ての単体作用素。使われ方：組み立ての単体的自然性。 -/
lemma oneDirectionAssemblyIndex_naturality (r : ℕ) {d e : SimplexCategoryᵒᵖ}
    (f : d ⟶ e) (α : d.unop ⟶ ⦋1⦌) :
    oneDirectionAssemblyIndex r d α ≫ (multiIndexDiagonal (r + 1)).map f =
      (oneDirectionIndex r).map ((multiIndexDiagonal r).map f) ≫
        oneDirectionAssemblyIndex r e (f.unop ≫ α) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change α.op ≫ f = 𝟙 _ ≫ (f.unop ≫ α).op
    rw [Category.id_comp]
    rfl
  · change 𝟙 d ≫ f = f ≫ 𝟙 e
    simp

/-- 概要：一次方向の区間から全反復の対角への写像。
方針：α による添字の射を core の関手で写し、内側の単体を保つ。
規約：Kan 置換前の厳密な写像。使われ方：境界商に降ろす cylinder。 -/
def coordinateDiagonalAssembly (r : ℕ)
    (M : (Fin (r + 1) → SimplexCategoryᵒᵖ) ⥤ SSet.{u}) :
    (Δ[1] : SSet.{u}) ⊗
      simplicialDiagonalFunctor.obj (multiIndexDiagonal r ⋙ oneDirectionIndex r ⋙ M) ⟶
      simplicialDiagonalFunctor.obj (multiIndexDiagonal (r + 1) ⋙ M) where
  app d := ↾fun z =>
    (M.map
      (oneDirectionAssemblyIndex r d (stdSimplex.objEquiv z.1))).app d z.2
  naturality {d e} f := by
    apply ConcreteCategory.hom_ext
    intro z
    symm
    change (M.obj ((multiIndexDiagonal (r + 1)).obj e)).map f
      (((M.map
        (oneDirectionAssemblyIndex r d (stdSimplex.objEquiv z.1)) ≫
        M.map ((multiIndexDiagonal (r + 1)).map f)).app d) z.2) =
      (M.map
        (oneDirectionAssemblyIndex r e (f.unop ≫ stdSimplex.objEquiv z.1))).app e
          ((M.obj
            ((oneDirectionIndex r).obj ((multiIndexDiagonal r).obj e))).map f
              ((M.map
                ((oneDirectionIndex r).map ((multiIndexDiagonal r).map f))).app d z.2))
    rw [← CategoryTheory.Functor.map_comp, oneDirectionAssemblyIndex_naturality,
      CategoryTheory.Functor.map_comp]
    exact ConcreteCategory.congr_hom
      ((M.map
        (oneDirectionAssemblyIndex r e (f.unop ≫ stdSimplex.objEquiv z.1))).naturality f).symm
      ((M.map
        ((oneDirectionIndex r).map ((multiIndexDiagonal r).map f))).app d z.2)

/-- 概要：反復 S の一次方向の区間から全反復の対角への写像。
方針：一般の多単体図式の組み立てに反復 core S を代入する。
規約：Kan 置換前の写像。使われ方：全零境界商への降下。 -/
def multiDiagonalAssembly (r : ℕ) (X : StableModel.{u}) :
    (Δ[1] : SSet.{u}) ⊗ (oneDirectionRealizationFunctor r).obj X ⟶
      multiDiagonalCoreSConstruction (r + 1) X :=
  coordinateDiagonalAssembly r (multiCoreSConstruction (r + 1) X)

/-- 概要：反復の組み立ては入力の射と可換。
方針：添字の射に対する多単体図式の自然性を評価する。
規約：全 cofiber 保存射。使われ方：構造射の関手性。 -/
lemma coordinateDiagonalAssembly_naturality (r : ℕ)
    {M N : (Fin (r + 1) → SimplexCategoryᵒᵖ) ⥤ SSet.{u}} (f : M ⟶ N) :
    ((Δ[1] : SSet.{u}) ◁ simplicialDiagonalFunctor.map
      (Functor.whiskerLeft (multiIndexDiagonal r) (Functor.whiskerLeft (oneDirectionIndex r) f))) ≫
        coordinateDiagonalAssembly r N =
      coordinateDiagonalAssembly r M ≫ simplicialDiagonalFunctor.map
        (Functor.whiskerLeft (multiIndexDiagonal (r + 1)) f) := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro z
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (f.naturality
      (oneDirectionAssemblyIndex r d (stdSimplex.objEquiv z.1))) d).symm z.2

/-- 概要：反復 S の組み立ては入力の射と可換。
方針：一般の多単体図式の自然性に入力の射を代入する。
規約：全 cofiber 保存射。使われ方：構造射の関手性。 -/
lemma multiDiagonalAssembly_naturality (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    ((Δ[1] : SSet.{u}) ◁ (oneDirectionRealizationFunctor r).map f) ≫
        multiDiagonalAssembly r Y =
      multiDiagonalAssembly r X ≫ (multiRealizationFunctor (r + 1)).map f :=
  coordinateDiagonalAssembly_naturality r ((multiCoreSConstructionFunctor (r + 1)).map f)

/-- 概要：定値の一次方向の射は第零方向の自己射で固定される。
方針：先頭で定値写像の合成を計算し、残りは恒等射。
規約：端点は 0 または 1。使われ方：端点が零境界に属する証明。 -/
lemma oneDirectionAssemblyIndex_constant_fixed (r : ℕ) (d : SimplexCategoryᵒᵖ) (i : Fin 2) :
    oneDirectionAssemblyIndex r d (SimplexCategory.const d.unop ⦋1⦌ i) ≫
        zeroDirectionsIndexEndomorphism {(0 : Fin (r + 1))} (fun _ => d) =
      oneDirectionAssemblyIndex r d (SimplexCategory.const d.unop ⦋1⦌ i) := by
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · simp [oneDirectionAssemblyIndex, zeroDirectionsIndexEndomorphism,
      zeroDirectionsIndexRetraction, zeroDirectionsIndexNat, zeroCoordinateRetraction,
      zeroCoordinateNat]
    rfl
  · change 𝟙 d ≫ zeroCoordinateEndomorphism j.succ
      (decide (j.succ ∈ ({0} : Finset (Fin (r + 1))))) (fun _ => d) = 𝟙 d
    have hb : decide (j.succ ∈ ({0} : Finset (Fin (r + 1)))) = false := by simp
    rw [hb]
    simp [zeroCoordinateEndomorphism, zeroCoordinateRetraction, zeroCoordinateNat]

end SerrePositivity.KST.SConstruction
