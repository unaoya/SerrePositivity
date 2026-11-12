module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.KanLimits
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyProduct
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.HomotopyZeroRelations
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopyIsomorphism

/-!
概要：Kan 複体の二項積の全基点・全次数のホモトピー類を分解する。
方針：代表単体と充填関係を成分ごとに組み合わせ、零次数も同じ方法で扱う。
規約：L9 の KanHomotopy と KanPiIsomorphism をそのまま使う。
使われ方：BF 1978 §2、Kerodon §3.2.2（Tag 00VJ）、HTT 4.2.4.1 の Sp の積の Ω 条件の検証。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.KST.Spectra
open scoped _root_.Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

noncomputable section

/-- 概要：二つの境界定数単体を積の境界定数単体へ組み合わせる。
方針：単体の写像を直積へ持ち上げ、境界の二つの射影を検査する。
規約：零次数も含み、Kan 性は不要。
使われ方：Kerodon §3.2.2（Tag 00VJ） の積のホモトピー類の代表の構成。 -/
def prodPointedSimplex {X Y : SSet.{u}} {n : ℕ} {x : X _⦋0⦌} {y : Y _⦋0⦌}
    (f : X.PtSimplex n x) (g : Y.PtSimplex n y) : (X ⊗ Y).PtSimplex n (x, y) where
  map := lift f.map g.map
  comm := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [comp_lift, lift_fst, f.comm, SSet.const_comp]
      rfl
    · simp only [comp_lift, lift_snd, g.comm, SSet.const_comp]
      rfl

/-- 概要：組み合わせた境界定数単体の第一射影は元の第一の単体。
方針：相対射の写像の等式と直積への持ち上げの射影則を使う。
規約：全次数。
使われ方：Kerodon §3.2.2（Tag 00VJ） の積の代表の射影の計算。 -/
lemma prodPointedSimplex_fst {X Y : SSet.{u}} {n : ℕ} {x : X _⦋0⦌} {y : Y _⦋0⦌}
    (f : X.PtSimplex n x) (g : Y.PtSimplex n y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (fst X Y) rfl (prodPointedSimplex f g) = f := by
  ext : 1
  exact lift_fst _ _

/-- 概要：組み合わせた境界定数単体の第二射影は元の第二の単体。
方針：相対射の写像の等式と直積への持ち上げの射影則を使う。
規約：全次数。
使われ方：Kerodon §3.2.2（Tag 00VJ） の積の代表の射影の計算。 -/
lemma prodPointedSimplex_snd {X Y : SSet.{u}} {n : ℕ} {x : X _⦋0⦌} {y : Y _⦋0⦌}
    (f : X.PtSimplex n x) (g : Y.PtSimplex n y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (snd X Y) rfl (prodPointedSimplex f g) = g := by
  ext : 1
  exact lift_snd _ _

/-- 概要：積のホモトピー類を二つの射影の像へ送る標準写像。
方針：L9 の各次数の誘導写像を組にする。
規約：指定基点は (x,y)、零次数も含む。
使われ方：BF 1978 §2 の積の Ω 条件を成分ごとに検査する射。 -/
def kanHomotopyProdMap {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    (n : ℕ) (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (X ⊗ Y) n (x, y) → _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy X n x × _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy Y n y :=
  fun a ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (fst X Y) rfl a, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (snd X Y) rfl a)

/-- 概要：積の全基点のホモトピー類は二つの射影の像と全単射に対応する。
方針：単射性は二つの充填関係を積へ組み、全射性は代表単体を積へ組む。
規約：n は全自然数次数で、零次数も除外しない。
使われ方：Kerodon §3.2.2（Tag 00VJ）、BF 1978 §2 の有限積による Ω 条件の保存。 -/
lemma kanHomotopyProdMap_bijective {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    (n : ℕ) (x : X _⦋0⦌) (y : Y _⦋0⦌) : Function.Bijective (kanHomotopyProdMap n x y) := by
  constructor
  · intro a b h
    obtain ⟨f, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.KanHomotopy.mk_surjective n a
    obtain ⟨g, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.KanHomotopy.mk_surjective n b
    have hx := congrArg Prod.fst h
    have hy := congrArg Prod.snd h
    simp only [kanHomotopyProdMap, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_mk] at hx hy
    obtain ⟨rx⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.KanHomotopy.mk_eq_iff_relStruct n _ _ 0).mp hx
    obtain ⟨ry⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.KanHomotopy.mk_eq_iff_relStruct n _ _ 0).mp hy
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.sound (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.prodRelStruct rx ry)
  · rintro ⟨a, b⟩
    obtain ⟨f, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.KanHomotopy.mk_surjective n a
    obtain ⟨g, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.KanHomotopy.mk_surjective n b
    refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk n (prodPointedSimplex f g), ?_⟩
    apply Prod.ext
    · change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (fst X Y) rfl _ = _
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_mk, prodPointedSimplex_fst]
    · change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (snd X Y) rfl _ = _
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_mk, prodPointedSimplex_snd]

/-- 概要：積の全基点の全次数のホモトピー類の標準全単射。
方針：実際の二つの射影から作った全単射を Equiv へ束ねる。
規約：順写像は kanHomotopyProdMap そのもの。
使われ方：Kerodon §3.2.2（Tag 00VJ）、Sp の積の Ω 条件の成分による検証。 -/
def kanHomotopyProdEquiv {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    (n : ℕ) (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (X ⊗ Y) n (x, y) ≃ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy X n x × _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy Y n y :=
  Equiv.ofBijective _ (kanHomotopyProdMap_bijective n x y)

/-- 概要：積のホモトピー類の分解は二つの射の直積と可換。
方針：二つの射影で検査し、誘導写像の合成則と直積の射影の自然性を使う。
規約：全基点・全自然数次数での実際の写像の等式。
使われ方：BF 1978 §2、積の射が Ω 条件の π_* 同型を保つことの検証。 -/
lemma kanHomotopyProdMap_naturality {X Y X' Y' : SSet.{u}}
    [KanComplex X] [KanComplex Y] [KanComplex X'] [KanComplex Y']
    (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ) (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (X ⊗ Y) n (x, y)) :
    kanHomotopyProdMap n (f.app _ x) (g.app _ y)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (f ⊗ₘ g) rfl a) =
      Prod.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n f rfl) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n g rfl)
        (kanHomotopyProdMap n x y a) := by
  apply Prod.ext
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (fst X' Y') rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (f ⊗ₘ g) rfl a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n f rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (fst X Y) rfl a)
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_comp n (f ⊗ₘ g) rfl (fst X' Y') rfl rfl,
      ← _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_comp n (fst X Y) rfl f rfl rfl]
    simp only [tensorHom_fst]
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (snd X' Y') rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (f ⊗ₘ g) rfl a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n g rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (snd X Y) rfl a)
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_comp n (f ⊗ₘ g) rfl (snd X' Y') rfl rfl,
      ← _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_comp n (snd X Y) rfl g rfl rfl]
    simp only [tensorHom_snd]

/-- 概要：全基点の π_* 同型の二項積も全基点の π_* 同型。
方針：全次数の積の分解の自然性と二つの誘導写像の全単射性を使う。
規約：零次数を含み、指定基点だけに条件を弱めない。
使われ方：BF 1978 §2、HTT 4.2.4.1 の Sp の二項積の Ω 条件の保存。 -/
lemma kanPiIsomorphism_tensor {X Y X' Y' : SSet.{u}}
    [KanComplex X] [KanComplex Y] [KanComplex X'] [KanComplex Y']
    {f : X ⟶ X'} {g : Y ⟶ Y'} (hf : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f) (hg : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism g) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (f ⊗ₘ g) := by
  rintro ⟨x, y⟩ n
  have hp : Function.Bijective
      (Prod.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n f (x := x) rfl) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n g (x := y) rfl)) :=
    (hf x n).prodMap (hg y n)
  have hc :
      kanHomotopyProdMap n (f.app _ x) (g.app _ y) ∘
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (f ⊗ₘ g) (x := (x, y)) rfl =
        Prod.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n f rfl) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n g rfl) ∘
          kanHomotopyProdMap n x y := by
    funext a
    exact kanHomotopyProdMap_naturality f g n x y a
  have hb := hp.comp (kanHomotopyProdMap_bijective n x y)
  rw [← hc] at hb
  exact hb.of_comp_left (kanHomotopyProdMap_bijective n (f.app _ x) (g.app _ y)).injective

end

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
