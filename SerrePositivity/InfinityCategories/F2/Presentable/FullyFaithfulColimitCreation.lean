module

public import SerrePositivity.InfinityCategories.F2.Presentable.EquivalenceColimits
public import SerrePositivity.InfinityCategories.F2.Ind.FullCoconeLift
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulEquivalence
public import SerrePositivity.InfinityCategories.Core.ColimitDiagramIso
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentCoconeTransport

/-!
概要：充満忠実な関手の像の余極限頂点が元の像と同型なら元の余極限が存在する。
方針：同型を含む頂点像の全部分圏へ因子化し、同値の逆で持ち上げた余錐を戻す。
規約：元の図式と関手を保持し、像の余極限の存在だけでは結論しない。
使われ方：全 Hom 係数族の表現可能性から局所 Kan 余極限を構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：充満忠実な像の指定余極限の頂点が同型を含む頂点像にあれば元の余極限が存在する。
方針：像の全部分複体で余錐を持ち上げ、因子化の同値を逆にたどる。
規約：元の任意の小さい形状を変更しない。
使われ方：表現可能な全 Hom 極限からの余極限の存在。 -/
lemma hasColimit_of_fullyFaithful_image_colimit_iso
    {K A B : SSet.{u}} [Quasicategory A] [Quasicategory B]
    (F : A ⟶ B) (hF : IsFullyFaithful F) (p : K ⟶ A)
    (c : JoinCocone (p ≫ F)) (hc : IsColimitCone c)
    (hvertex : ∃ a : A _⦋0⦌, Nonempty (VertexIso
      (F.app (Opposite.op ⦋0⦌) a) c.vertex)) : HasColimit p := by
  let P : B _⦋0⦌ → Prop := fun b ↦ ∃ a, Nonempty (VertexIso
    (F.app (Opposite.op ⦋0⦌) a) b)
  let E : SSet.{u} := fullSubcomplexOnVertices B P
  let q : A ⟶ E := fullSubcomplexLift P F (fun a ↦ ⟨a, ⟨Iso.refl _⟩⟩)
  have hq : IsFullyFaithful q := by
    apply (isFullyFaithful_fullSubcomplexOnVertices_ι B P).cancel_right
    rw [show q ≫ (fullSubcomplexOnVertices B P).ι = F from fullSubcomplexLift_ι _ _ _]
    exact hF
  have hess : IsEssentiallySurjective q := by
    intro b
    obtain ⟨a, ⟨ea⟩⟩ := fullSubcomplexOnVertices_vertex b
    have ee : VertexIso
        ((fullSubcomplexOnVertices B P).ι.app (Opposite.op ⦋0⦌)
          (q.app (Opposite.op ⦋0⦌) a))
        ((fullSubcomplexOnVertices B P).ι.app (Opposite.op ⦋0⦌) b) := ea
    exact ⟨a, ⟨(isFullyFaithful_fullSubcomplexOnVertices_ι B P).toHoFullyFaithful.preimageIso ee⟩⟩
  let e := (isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective q hq hess).choose
  have hdiag : (p ≫ q) ≫ (fullSubcomplexOnVertices B P).ι = p ≫ F := by
    rw [Category.assoc, fullSubcomplexLift_ι]
  let c' := coherentCoconeOfDiagramEq hdiag.symm c
  have hc' : IsColimitCone c' :=
    (coherentCoconeOfDiagramEq_isColimit_iff hdiag.symm c).mp hc
  have hvertex' : P c'.vertex := hvertex
  let d := Ind.fullCoconeLift P (p ≫ q) c' hvertex'
  have hd := Ind.fullCoconeLift_isColimit P (p ≫ q) c' hvertex' hc'
  have hi := (equivalence_isColimitCone_iff e.symm.isQCatEquivalence d).mp hd
  have he : FunctorIso ((p ≫ q) ≫ e.inv) p := by
    have hh := e.homInvIso.precomp p
    change FunctorIso (p ≫ (e.hom ≫ e.inv)) (p ≫ 𝟙 A) at hh
    rw [show e.hom = q from rfl, Category.comp_id] at hh
    simpa only [Category.assoc] using hh
  exact (hasColimit_iff_of_functorIso he).mp ⟨mapJoinCocone e.inv d, hi⟩

end SerrePositivity.InfinityCategories.F2.Presentable
