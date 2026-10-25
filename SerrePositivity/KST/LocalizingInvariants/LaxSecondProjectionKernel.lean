module

public import SerrePositivity.KST.LocalizingInvariants.LaxCounitCComparison
public import SerrePositivity.KST.LocalizingInvariants.VerdierSequence

/-!
概要：元の lax pullback の第二射影の核を、C 包含の本質像と同定する。
方針：第二成分が零の点では元の C 随伴単位が可逆であることを使う。
規約：元の包含と射影を保持し、核を生成する仮定を追加しない。
使われ方：D2 の gluing 商の実核と Verdier 列の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.LaxInclusion
variable {C D E : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)

lemma snd_kernel (x : (laxCategory p q).obj _⦋0⦌) :
    IsZeroVertex ((laxSnd p q).hom.app (Opposite.op ⦋0⦌) x) ↔
      x ∈ essentialImage (exactFromC p q) := by
  constructor
  · intro hx
    let c := (laxFst p q).hom.app (Opposite.op ⦋0⦌) x
    have := LaxCounit.fromC_unit_component_isIso p q x hx
    exact ⟨c, ⟨(asIso (functorHomEvaluate (fromCAdjunction p q).unitHom x)).symm⟩⟩
  · rintro ⟨c, ⟨e⟩⟩
    have hz : IsZeroVertex ((laxSnd p q).hom.app (Opposite.op ⦋0⦌)
        ((fromC p q).app (Opposite.op ⦋0⦌) c)) := by
      change IsZeroVertex ((F2.laxPullbackSnd p.hom q.hom).app (Opposite.op ⦋0⦌) _)
      rw [fromC_snd_vertex]
      exact (chosenZeroVertex D.obj).isZero
    exact hz.of_vertexIso (VertexIso.map e (laxSnd p q).hom)

end SerrePositivity.KST.LocalizingInvariants.LaxInclusion
