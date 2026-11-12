module
public import SerrePositivity.KST.SConstruction.Cofinality.WideComponentGroup

/-!
概要：元の同じ S 標的の完全三角形は wide 成分の加法関係を与える。
方針：第一対象のシフトの可縮三角形を加え、第一対象を本質像へ入れて第二射を分母にする。
規約：三角形の各対象と元の成分評価を保持する。
使われ方：三角圏 K₀ の普遍性による障害群への逆写像。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory Limits Pretriangulated SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial ZeroObject

/-- 概要：二つの三角形の対象の二項積を標準双積へ写す。
方針：二点添字の関数を成分で照合し、標準積と双積の同型を使う。
規約：同じ全多次数のホモトピー圏で構成する。
使われ方：三角形の積の三対象の成分表示。 -/
private def completionTriangleProductObjectIso (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) (Y : StableModel.{u})
    (T U : Triangle (hoFunctor.obj (((multiSEndofunctor r).obj ι).obj Y).carrier))
    (F : Triangle (hoFunctor.obj (((multiSEndofunctor r).obj ι).obj Y).carrier) →
      hoFunctor.obj (((multiSEndofunctor r).obj ι).obj Y).carrier) :
    Limits.piObj (fun j : WalkingPair => F (pairFunction T U j)) ≅ F T ⊞ F U := by
  have he : (fun j : WalkingPair => F (pairFunction T U j)) = pairFunction (F T) (F U) := by
    funext j
    cases j <;> rfl
  exact eqToIso (congrArg (fun q : WalkingPair →
      hoFunctor.obj (((multiSEndofunctor r).obj ι).obj Y).carrier => Limits.piObj q) he) ≪≫
    (biprod.isoProd (F T) (F U)).symm

/-- 概要：完全三角形の第二対象と第一対象のシフトの和は第三対象と同じ成分。
方針：シフト対象の可縮三角形との積を取り、D-22 により第一対象が像に入ると示す。
規約：元の三角形の第二射に対応する分母で成分を比較する。
使われ方：完全三角形の加法関係の証明。 -/
lemma completionWideTriangle_stabilized (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (T : Triangle (hoFunctor.obj (((multiSEndofunctor r).obj ι).obj Y).carrier))
    (hT : T ∈ distTriang _) :
    completionWideObjectClass r ι f hf (T.obj₂ ⊞
      (shiftFunctor (hoFunctor.obj (((multiSEndofunctor r).obj ι).obj Y).carrier)
        (1 : ℤ)).obj T.obj₁) = completionWideObjectClass r ι f hf T.obj₃ := by
  let C := hoFunctor.obj (((multiSEndofunctor r).obj ι).obj Y).carrier
  let A := (shiftFunctor C (1 : ℤ)).obj T.obj₁
  let U := contractibleTriangle A
  let V := productTriangle (pairFunction T U)
  have hV : V ∈ distTriang C := productTriangle_distinguished (pairFunction T U) (by
    intro j
    cases j
    · exact hT
    · exact contractible_distinguished A)
  let e₁ := completionTriangleProductObjectIso r ι Y T U Triangle.obj₁
  let e₂ := completionTriangleProductObjectIso r ι Y T U Triangle.obj₂
  let e₃ := completionTriangleProductObjectIso r ι Y T U Triangle.obj₃ ≪≫
    (isoBiprodZero (C := C) (X := T.obj₃) (isZero_zero C)).symm
  let P := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure (LocalizingInvariants.completionEssentialImage
    (((multiSEndofunctor r).obj ι).map f).val)
  obtain ⟨a, ⟨ea⟩⟩ := multiSBiprodShift_mem_image_of_completion r ι f hf T.obj₁
  obtain ⟨a, rfl⟩ := Truncated.HomotopyCategory.mk_surjective a
  have hA : P (T.obj₁ ⊞ A) := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure.of_mem ⟨a, ⟨ea.symm⟩⟩
  have h₁ : P V.obj₁ := P.prop_of_iso e₁.symm hA
  have hW : P.trW V.mor₂ := ObjectProperty.trW.mk' P hV h₁
  exact (completionWideObjectClass_iso r ι f hf e₂).symm.trans
    ((completionWideObjectClass_eq_of_trW r ι f hf V.mor₂ hW).trans
      (completionWideObjectClass_iso r ι f hf e₃))

/-- 概要：元の完全三角形の成分は加法関係を満たす。
方針：安定化した分母比較と双積懸垂の零性を可換群で消去する。
規約：明示的に構成した元の成分群の和を使う。
使われ方：元の三角圏 K₀ から成分群への降下。 -/
lemma completionWideTriangle_additivity (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (T : Triangle (hoFunctor.obj (((multiSEndofunctor r).obj ι).obj Y).carrier))
    (hT : T ∈ distTriang _) :
    completionWideObjectClass r ι f hf T.obj₂ = completionWideAdd r ι f hf
      (completionWideObjectClass r ι f hf T.obj₁) (completionWideObjectClass r ι f hf T.obj₃) := by
  let : AddCommGroup (SSet.π₀ (LocalizingInvariants.completionCofiberWide
    (((multiSEndofunctor r).obj ι).map f).val : SSet.{u})) := completionWideAddCommGroup r ι f hf
  let c := completionWideObjectClass r ι f hf
  let A := (shiftFunctor (hoFunctor.obj (((multiSEndofunctor r).obj ι).obj Y).carrier)
    (1 : ℤ)).obj T.obj₁
  have hB : c T.obj₂ + c A = c T.obj₃ :=
    (completionWideAdd_objectClass r ι f hf T.obj₂ A).trans
      (completionWideTriangle_stabilized r ι f hf T hT)
  have hA : c T.obj₁ + c A = 0 :=
    (completionWideAdd_objectClass r ι f hf T.obj₁ A).trans
      (completionWideObjectClass_biprod_shift_zero r ι f hf T.obj₁)
  change c T.obj₂ = c T.obj₁ + c T.obj₃
  calc
    c T.obj₂ = c T.obj₂ + (c T.obj₁ + c A) := by rw [hA, add_zero]
    _ = c T.obj₁ + (c T.obj₂ + c A) := by abel
    _ = c T.obj₁ + c T.obj₃ := congrArg (fun z => c T.obj₁ + z) hB

end SerrePositivity.KST.SConstruction.Cofinality
