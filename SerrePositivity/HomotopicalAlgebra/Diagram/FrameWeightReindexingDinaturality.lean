module

public import SerrePositivity.HomotopicalAlgebra.Diagram.FrameWeightReindexing
public import SerrePositivity.HomotopicalAlgebra.Diagram.FrameWeightFunctoriality

/-!
概要：添字自然変換による重みと係数の移送は、指定実現の添字変更後に一致する。
方針：指定随伴で転置し、元の単位の添字自然性を各成分で使う。
使われ方：HTT 4.2.4.4、RR02(a)の余単位の円柱と元の実現比較の照合。
規約：元の実現対象・比較射・係数移送を保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w u
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.DiagramModel.FrameWeightRealization
variable {K L : Type w} [SmallCategory K] [SmallCategory L]
  {C : Type u} [Category.{w} C] [HasColimitsOfSize.{w, w} C]
  {P Q : L ⥤ K} (α : P ⟶ Q) (A : K ⥤ SimplexCategory ⥤ C)
  (W : Kᵒᵖ ⥤ SSet.{w})

/-- 重みの反変移送と係数の共変移送の、指定添字変更に対する同じ法則。 -/
lemma reindexMap_dinaturality :
    (functor L (P ⋙ A)).map (Functor.whiskerRight (NatTrans.op α) W) ≫
        reindexMap P A W =
      (map L (Functor.whiskerRight α A)).app (Q.op ⋙ W) ≫ reindexMap Q A W := by
  apply ((adjunction L (P ⋙ A)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, reindexMap_homEquiv,
    homEquiv_frame_naturality, reindexMap_homEquiv]
  apply NatTrans.ext
  funext e
  simpa [homReindexIso] using
    ((adjunction K A).unit.app W).naturality (α.app e.unop).op

end SerrePositivity.DiagramModel.FrameWeightRealization
