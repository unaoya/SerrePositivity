module
public import SerrePositivity.InfinityCategories.Core.ColimitExistenceTransfer

public import SerrePositivity.InfinityCategories.HomotopyLimits.ColimitAttachmentDiagram

/-!
概要：部分余極限頂点を付加した図式に、元の余錐を頂点も含めて保って延長する。
方針：付加に沿う coslice の制限の trivial Kan fibration 性で、指定した余錐を持ち上げる。
規約：元の余錐の余極限性は延長の存在には不要。余極限性の保存と反映は別に示す。
使われ方：部分図式の余極限対象の間の射と、その脚を含む coherent な三角形の構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {A C X : SSet.{u}} {p : A ⟶ X}

/-- 元の余錐は、部分余極限頂点を付加した図式へ、制限と頂点を厳密に保って延長できる。 -/
lemma exists_colimitAttachedCocone (c : JoinCocone p) (hc : IsColimitCone c)
    (i : A ⟶ C) (F : C ⟶ X) (hi : i ≫ F = p) (d : JoinCocone F) :
    ∃ e : JoinCocone (colimitAttachedDiagram c i F hi),
      coherentCoconeOfDiagramEq (colimitAttachedDiagram_right c i F hi)
        (e.restrict (pushout.inr (joinInl A Δ[0]) i)) = d ∧ e.vertex = d.vertex := by
  have := colimitAttachedDiagram_restriction_trivialKanFibration c hc i F hi
  let d' := coherentCoconeOfDiagramEq (colimitAttachedDiagram_right c i F hi).symm d
  obtain ⟨e, he, hv⟩ := exists_cocone_extension_of_trivialRestriction
    (colimitAttachedDiagram c i F hi) (pushout.inr (joinInl A Δ[0]) i) d'
  refine ⟨e, ?_, hv.trans (coherentCoconeOfDiagramEq_vertex _ d)⟩
  rw [he]
  apply Subtype.ext
  rw [coherentCoconeOfDiagramEq_val, coherentCoconeOfDiagramEq_val]

/-- 元の指定した余錐を保持する、付加後の図式の実際の余錐を選ぶ。 -/
def colimitAttachedCocone (c : JoinCocone p) (hc : IsColimitCone c)
    (i : A ⟶ C) (F : C ⟶ X) (hi : i ≫ F = p) (d : JoinCocone F) :
    JoinCocone (colimitAttachedDiagram c i F hi) :=
  (exists_colimitAttachedCocone c hc i F hi d).choose

/-- 選んだ延長の元の図式への制限は、指定した余錐そのもの。 -/
lemma colimitAttachedCocone_restrict (c : JoinCocone p) (hc : IsColimitCone c)
    (i : A ⟶ C) (F : C ⟶ X) (hi : i ≫ F = p) (d : JoinCocone F) :
    coherentCoconeOfDiagramEq (colimitAttachedDiagram_right c i F hi)
      ((colimitAttachedCocone c hc i F hi d).restrict
        (pushout.inr (joinInl A Δ[0]) i)) = d :=
  (exists_colimitAttachedCocone c hc i F hi d).choose_spec.1

/-- 付加後の余錐の頂点は、元の指定した余錐の頂点と一致する。 -/
lemma colimitAttachedCocone_vertex (c : JoinCocone p) (hc : IsColimitCone c)
    (i : A ⟶ C) (F : C ⟶ X) (hi : i ≫ F = p) (d : JoinCocone F) :
    (colimitAttachedCocone c hc i F hi d).vertex = d.vertex :=
  (exists_colimitAttachedCocone c hc i F hi d).choose_spec.2

/-- 付加後の選んだ余錐の余極限性は、元の指定した余錐の余極限性と同値。 -/
lemma colimitAttachedCocone_isColimit_iff [Quasicategory X]
    (c : JoinCocone p) (hc : IsColimitCone c) (i : A ⟶ C)
    (F : C ⟶ X) (hi : i ≫ F = p) (d : JoinCocone F) :
    IsColimitCone (colimitAttachedCocone c hc i F hi d) ↔ IsColimitCone d := by
  rw [isColimitCone_iff_restrict_of_colimit_attachment c hc i _ _
    (IsPushout.of_hasPushout _ _) (colimitAttachedDiagram_left c i F hi) _]
  rw [coherentCoconeOfDiagramEq_isColimit_iff
    (colimitAttachedDiagram_right c i F hi), colimitAttachedCocone_restrict]

end
end SerrePositivity.InfinityCategories.HomotopyLimits
