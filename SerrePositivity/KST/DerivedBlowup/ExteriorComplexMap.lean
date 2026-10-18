module

public import SerrePositivity.KST.DerivedBlowup.ExteriorDegreeMap

/-!
概要：KST Def3.1 の微分に適合する基底変換を整数次数の Koszul 複体の射へ持ち上げる。
方針：次数別外積写像と収縮の可換性から chain map を作り、零延長する。
規約：同一基底環上。微分適合条件は証明として明示する。
使われ方：チャートの複体の同型と三重重なりでの cocycle。
-/

@[expose] public noncomputable section

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory

variable {R : Type u} [CommRing R]
  {M N P : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

/-- 概要：微分を保つ生成元写像から外積 Koszul chain map を作る。
方針：各次数の外積写像を使い、収縮との可換性を chain 条件にする。
規約：KST Def3.1、dN∘f=dM。使われ方：可逆基底変換を複体の射へ延長する。 -/
def exteriorKoszulChainMap (f : M →ₗ[R] N) (dM : M →ₗ[R] R) (dN : N →ₗ[R] R)
    (h : dN.comp f = dM) : exteriorKoszulChain dM ⟶ exteriorKoszulChain dN :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (exteriorDegreeMap f n)) (fun n => by
    dsimp only [exteriorKoszulChain]
    rw [ChainComplex.of_d, ChainComplex.of_d]
    ext z
    exact exteriorContraction_map f dM dN h z.val)

/-- 概要：chain map を非正整数次数の cochain map に延長する。
方針：複体形埋め込み n↦−n に沿う extendMap。
規約：KST Def3.1、零延長。使われ方：整数次数のチャート dg 模型の比較。 -/
def exteriorKoszulCochainMap (f : M →ₗ[R] N) (dM : M →ₗ[R] R) (dN : N →ₗ[R] R)
    (h : dN.comp f = dM) : exteriorKoszulCochain dM ⟶ exteriorKoszulCochain dN :=
  HomologicalComplex.extendMap (exteriorKoszulChainMap f dM dN h)
    (ComplexShape.embeddingUpIntLE 0)

/-- 概要：外積 Koszul chain map は生成元の恒等写像を保つ。
方針：各外積次数の map_id を使う。
規約：KST Def3.1。使われ方：複体同型の両側逆。 -/
theorem exteriorKoszulChainMap_id (d : M →ₗ[R] R) (h : d.comp LinearMap.id = d) :
    exteriorKoszulChainMap LinearMap.id d d h = 𝟙 (exteriorKoszulChain d) := by
  ext n z
  apply Subtype.ext
  exact AlgHom.congr_fun ExteriorAlgebra.map_id z.val

/-- 概要：外積 Koszul chain map は生成元写像の合成を保つ。
方針：各外積次数の合成公式で確認する。
規約：KST §3.1、適合性の証明項の選択には依存しない。
使われ方：チャート遷移の cocycle と可逆性。 -/
theorem exteriorKoszulChainMap_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (dM : M →ₗ[R] R) (dN : N →ₗ[R] R) (dP : P →ₗ[R] R)
    (hf : dN.comp f = dM) (hg : dP.comp g = dN) (hgf : dP.comp (g.comp f) = dM) :
    exteriorKoszulChainMap f dM dN hf ≫ exteriorKoszulChainMap g dN dP hg =
      exteriorKoszulChainMap (g.comp f) dM dP hgf := by
  ext n z
  apply Subtype.ext
  exact AlgHom.congr_fun (ExteriorAlgebra.map_comp_map f g) z.val

end SerrePositivity.KST.DerivedBlowup
