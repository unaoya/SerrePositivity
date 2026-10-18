module
public import SerrePositivity.InfinityCategories.Stable.ExactFunctor
public import SerrePositivity.InfinityCategories.Stable.Suspension

/-! # 完全関手による suspension 図式の像

概要：完全関手を suspension 図式の族に作用させ、始点・終点の評価との可換性を示す。
方針：内部 Hom の後合成を頂点条件の全部分圏に制限する。
規約：全ての高次単体に自然な射を作る。使われ方：完全関手の懸垂比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：四角形の関手頂点の後合成は四角形の後合成に一致する。
方針：内部 Hom の零単体の評価を計算する。
規約：値域の仮定は不要。使われ方：suspension 図式の条件の保存。 -/
lemma squareDiagram_postcomp {X Y : SSet.{u}} (F : X ⟶ Y)
    (v : ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X) _⦋0⦌) :
    squareDiagram (((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).map F).app (Opposite.op ⦋0⦌) v) =
      squareDiagram v ≫ F := by
  rfl

/-- 概要：完全関手は suspension 図式の頂点条件を保つ。
方針：二つの零角と押し出し性を保存する。
規約：完全性以外の値域の仮定は不要。使われ方：図式の族への後合成。 -/
lemma IsExactFunctor.preservesSuspensionDiagramVertex {X Y : SSet.{u}}
    (F : X ⟶ Y) [IsExactFunctor F]
    (v : ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X) _⦋0⦌)
    (hv : IsSuspensionDiagramVertex v) :
    IsSuspensionDiagramVertex
      (((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).map F).app (Opposite.op ⦋0⦌) v) := by
  rcases hv with ⟨hz, hw, hp⟩
  unfold IsSuspensionDiagramVertex
  rw [squareDiagram_postcomp]
  exact ⟨IsExactFunctor.preservesZero (F := F) _ hz,
    IsExactFunctor.preservesZero (F := F) _ hw,
    IsExactFunctor.preservesCofiber (F := F) ⟨squareDiagram v, hz⟩ hp⟩

/-- 概要：完全関手は suspension 図式の族の単体的関手を誘導する。
方針：内部 Hom の後合成を全部分圏に持ち上げる。
規約：図式の全単体を写す。使われ方：懸垂との自然な交換同型。 -/
def exactFunctorSuspensionDiagrams {X Y : SSet.{u}} (F : X ⟶ Y) [IsExactFunctor F] :
    suspensionDiagrams X ⟶ suspensionDiagrams Y :=
  fullSubcomplexLift IsSuspensionDiagramVertex
    ((fullSubcomplexOnVertices _ IsSuspensionDiagramVertex).ι ≫
      (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).map F)
    (fun v ↦ IsExactFunctor.preservesSuspensionDiagramVertex F v.val
      (fullSubcomplexOnVertices_vertex v))

/-- 概要：suspension 図式の後合成は全ての角の評価と可換。
方針：内部 Hom の各単体の評価を計算する。
規約：単体的な射の厳密な等式。使われ方：始点を固定した図式比較。 -/
lemma exactFunctorSuspensionDiagrams_evaluation {X Y : SSet.{u}}
    (F : X ⟶ Y) [IsExactFunctor F] (i j : Fin 2) :
    exactFunctorSuspensionDiagrams F ≫ suspensionDiagramEvaluation Y i j =
      suspensionDiagramEvaluation X i j ≫ F := by
  rfl

/-- 概要：完全関手は指定した suspension 四角形を suspension 四角形へ写す。
方針：零角と cofiber 性を保存し、始点の等式を頂点写像で写す。
規約：像の始点は元の始点の像。使われ方：対象ごとの懸垂比較。 -/
def SuspensionSquare.map {X Y : SSet.{u}} {x : X _⦋0⦌}
    (s : SuspensionSquare x) (F : X ⟶ Y) [IsExactFunctor F] :
    SuspensionSquare (F.app (Opposite.op ⦋0⦌) x) where
  square := s.square ≫ F
  zero_corner := IsExactFunctor.preservesZero (F := F) _ s.zero_corner
  source_eq := congrArg (F.app (Opposite.op ⦋0⦌)) s.source_eq
  other_zero := IsExactFunctor.preservesZero (F := F) _ s.other_zero
  isPushout := IsExactFunctor.preservesCofiber (F := F) s.toZeroTriangle s.isPushout

/-- 概要：完全関手の前後で選んだ suspension 図式の族は可逆に比較できる。
方針：両方の族の始点が元の関手に厳密に一致することから、始点評価の可縮な fiber を使う。
規約：四角形の族全体の可逆二胞体。使われ方：懸垂比較の自然性。 -/
def exactFunctorSuspensionFamilyIso {X Y : SSet.{u}}
    [Quasicategory X] [IsStable X] [Quasicategory Y] [IsStable Y]
    (F : X ⟶ Y) [IsExactFunctor F] :
    FunctorIso ((suspensionDiagramSourceEquivalence X).inv ≫ exactFunctorSuspensionDiagrams F)
      (F ≫ (suspensionDiagramSourceEquivalence Y).inv) :=
  suspensionDiagramFamilyIso _ _ (by
    rw [Category.assoc, exactFunctorSuspensionDiagrams_evaluation,
      ← Category.assoc, suspensionDiagramSourceEquivalence_inv_source, Category.id_comp,
      Category.assoc, suspensionDiagramSourceEquivalence_inv_source, Category.comp_id])

/-- 概要：完全関手が誘導する h C の関手は懸垂と自然同型を介して可換。
方針：図式の族の可逆二胞体を右上で評価する。
規約：向きは Σ の後で関手を適用する側から、関手の後で Σ を適用する側。
使われ方：整数シフトの交換と三角関手。 -/
def exactFunctorSuspensionIso {X Y : SSet.{u}}
    [Quasicategory X] [IsStable X] [Quasicategory Y] [IsStable Y]
    (F : X ⟶ Y) [IsExactFunctor F] :
    suspensionFunctor X ⋙ (hoFunctor.map F).toFunctor ≅
      (hoFunctor.map F).toFunctor ⋙ suspensionFunctor Y := by
  have e := (FunctorIso.postcomp (exactFunctorSuspensionFamilyIso F)
    (suspensionDiagramEvaluation Y 1 1)).toNatIso
  rw [Category.assoc, exactFunctorSuspensionDiagrams_evaluation] at e
  simpa only [CategoryTheory.Functor.map_comp, Cat.Hom.comp_toFunctor,
    suspensionFunctor, QCatEquivalence.toHoEquivalence_inverse, CategoryTheory.Functor.assoc] using e

end SerrePositivity.InfinityCategories
