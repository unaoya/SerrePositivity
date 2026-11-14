module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.VertexPrescribedExtension
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.ContractibleKan

/-!
概要：可縮 Kan 複体からの単射に、全頂点の読出しを指定した厳密左逆を与える。
方針：単射の像上の逆写像と全頂点を、可縮 Kan 複体への相対延長で貼る。
規約：単射と頂点読出しの整合性は別途実構成する。
使われ方：Ind-S (9) の制御二胞体族の厳密切断。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 全頂点の読出しを保つ、可縮 Kan 始域への厳密な左逆。 -/
lemma contractibleKan_exists_retraction_with_vertices {L T : SSet.{u}}
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan L) (encode : L ⟶ T) [Mono encode]
    (read₀ : T _⦋0⦌ → L _⦋0⦌)
    (hr : ∀ l, read₀ (encode.app (Opposite.op ⦋0⦌) l) = l) :
    ∃ read : T ⟶ L, encode ≫ read = 𝟙 L ∧
      ∀ t, read.app (Opposite.op ⦋0⦌) t = read₀ t := by
  let A := Subcomplex.range encode
  let e := asIso (Subcomplex.toRange encode)
  obtain ⟨read, hread, hvertices⟩ := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.exists_extension_with_vertices A e.inv read₀ (by
    intro v
    have he := congrArg (fun f => f.app (Opposite.op ⦋0⦌) v) e.inv_hom_id
    have hv : encode.app (Opposite.op ⦋0⦌) (e.inv.app (Opposite.op ⦋0⦌) v) = v.val :=
      congrArg Subtype.val he
    rw [← hv, hr]) (fun _ _ _ => Or.inl (hc.isInitialVertex _))
  refine ⟨read, ?_, hvertices⟩
  calc
    encode ≫ read = e.hom ≫ A.ι ≫ read := rfl
    _ = e.hom ≫ e.inv := by rw [hread]
    _ = 𝟙 L := e.hom_inv_id

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
