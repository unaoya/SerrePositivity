module

public import SerrePositivity.HomologicalAlgebra.DirectedHomology
public import SerrePositivity.CommutativeAlgebra.Koszul

/-! # Koszul 構成と増大列

Koszul 複体を作る反復錐は、各次数で単射かつ被覆となる複体の増大列を保つ。
項の直積表示で確かめ、ホモロジーと有向極限の同型へ接続する。
-/

@[expose] public section

universe u

namespace SerrePositivity

open CategoryTheory Limits HomologicalComplex

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- 錐の項の直積表示における、射の自然性の順向き。 -/
lemma scalarConeXIsoProd_hom_naturality (a : R)
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q) (i : ℤ) :
    ((scalarConeFunctor a).map f).f i ≫ (scalarConeXIsoProd a Q i).hom =
      (scalarConeXIsoProd a P i).hom ≫
        ModuleCat.ofHom ((f.f (i+1)).hom.prodMap (f.f i).hom) := by
  apply (cancel_epi (scalarConeXIsoProd a P i).inv).mp
  rw [← Category.assoc, ← scalarConeXIsoProd_inv_naturality, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]

/-- 各項で単射な写像は、スカラー作用の錐を取っても各項で単射である。 -/
theorem scalarCone_map_injective (a : R)
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q)
    (hf : ∀ i, Function.Injective (f.f i)) (i : ℤ) :
    Function.Injective (((scalarConeFunctor a).map f).f i) := by
  intro x y hxy
  apply (scalarConeXIsoProd a P i).toLinearEquiv.injective
  have hn := scalarConeXIsoProd_hom_naturality a f i
  have hx := congrArg (fun f ↦ f.hom x) hn
  have hy := congrArg (fun f ↦ f.hom y) hn
  have he := (hx.symm.trans (congrArg ((scalarConeXIsoProd a Q i).hom) hxy)).trans hy
  exact Prod.ext (hf (i+1) (congrArg Prod.fst he)) (hf i (congrArg Prod.snd he))

variable (F : ℕ ⥤ CochainComplex (ModuleCat.{u} R) ℤ) (c : Cocone F)

/-- 二つの項の代表元を共通の段まで送れば、錐の項もその段から得られる。 -/
theorem scalarCone_cocone_cover (a : R)
    (hcover : ∀ i (x : c.pt.X i), ∃ n y, (c.ι.app n).f i y = x)
    (i : ℤ) (x : ((scalarConeFunctor a).obj c.pt).X i) :
    ∃ n y, (((scalarConeFunctor a).map (c.ι.app n)).f i) y = x := by
  let e := scalarConeXIsoProd a c.pt i
  obtain ⟨n, y, hy⟩ := hcover (i+1) (e.hom x).1
  obtain ⟨m, z, hz⟩ := hcover i (e.hom x).2
  let k := max n m
  let y' := (F.map (homOfLE (le_max_left n m))).f (i+1) y
  let z' := (F.map (homOfLE (le_max_right n m))).f i z
  refine ⟨k, (scalarConeXIsoProd a (F.obj k) i).inv (y', z'), ?_⟩
  have he := congrArg (fun f ↦ f.hom (y', z'))
    (scalarConeXIsoProd_inv_naturality a (c.ι.app k) i)
  change e.inv ((c.ι.app k).f (i+1) y', (c.ι.app k).f i z') =
    (((scalarConeFunctor a).map (c.ι.app k)).f i)
      ((scalarConeXIsoProd a (F.obj k) i).inv (y', z')) at he
  rw [← he]
  have hy' : (c.ι.app k).f (i+1) y' = (e.hom x).1 :=
    (congrArg (fun f ↦ f.f (i+1) y) (c.w (homOfLE (le_max_left n m)))).trans hy
  have hz' : (c.ι.app k).f i z' = (e.hom x).2 :=
    (congrArg (fun f ↦ f.f i z) (c.w (homOfLE (le_max_right n m)))).trans hz
  rw [hy', hz', Prod.mk.eta]
  exact e.toLinearEquiv.symm_apply_apply x

/-- Koszul 関手は、各次数での単射性を保つ。 -/
theorem koszulFunctor_map_injective {r : ℕ} (z : Fin r → R)
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q)
    (hf : ∀ i, Function.Injective (f.f i)) :
    ∀ i, Function.Injective (((koszulFunctor z).map f).f i) := by
  induction r with
  | zero => exact hf
  | succ r ih =>
    exact scalarCone_map_injective (z (Fin.last r)) _ (ih (Fin.init z))

/-- Koszul 関手は、各次数で有限段が全体を覆う性質を保つ。 -/
theorem koszulFunctor_cocone_cover {r : ℕ} (z : Fin r → R)
    (hcover : ∀ i (x : c.pt.X i), ∃ n y, (c.ι.app n).f i y = x) :
    ∀ i (x : ((koszulFunctor z).obj c.pt).X i),
      ∃ n y, (((koszulFunctor z).map (c.ι.app n)).f i) y = x := by
  induction r with
  | zero => exact hcover
  | succ r ih =>
    exact scalarCone_cocone_cover (F ⋙ koszulFunctor (Fin.init z))
      ((koszulFunctor (Fin.init z)).mapCocone c) (z (Fin.last r)) (ih (Fin.init z))

/-- 加群を零次に置いて Koszul 構成を施す関手。 -/
noncomputable def koszulModuleFunctor {r : ℕ} (z : Fin r → R) :
    ModuleCat.{u} R ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
  HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0 ⋙ koszulFunctor z

variable (G : ℕ ⥤ ModuleCat.{u} R) (d : Cocone G)

/-- 単一複体への埋め込みは単射を各次数で単射な射に送る。 -/
theorem single_map_injective {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (hf : Function.Injective f) (i : ℤ) :
    Function.Injective (((HomologicalComplex.single _ (.up ℤ) 0).map f).f i) := by
  by_cases hi : i = 0
  · subst i
    rw [HomologicalComplex.single_map_f_self]
    exact (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).toLinearEquiv.symm.injective.comp
      (hf.comp (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).toLinearEquiv.injective)
  · have := ModuleCat.subsingleton_of_isZero
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i hi)
    exact Function.injective_of_subsingleton _

/-- 各段の加群が全体を覆うとき、零次に置いた複体も各次数で全体を覆う。 -/
theorem single_cocone_cover
    (hcover : ∀ x : d.pt, ∃ n y, d.ι.app n y = x) (i : ℤ)
    (x : ((HomologicalComplex.single _ (.up ℤ) 0).obj d.pt).X i) :
    ∃ n y, (((HomologicalComplex.single _ (.up ℤ) 0).map (d.ι.app n)).f i) y = x := by
  by_cases hi : i = 0
  · subst i
    let e := HomologicalComplex.singleObjXSelf (.up ℤ) 0 d.pt
    obtain ⟨n, y, hy⟩ := hcover (e.hom x)
    refine ⟨n, (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (G.obj n)).inv y, ?_⟩
    rw [HomologicalComplex.single_map_f_self]
    change e.inv (d.ι.app n
      ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 (G.obj n)).hom
        ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 (G.obj n)).inv y))) = x
    have hc : (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (G.obj n)).hom
        ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 (G.obj n)).inv y) = y :=
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (G.obj n)).toLinearEquiv.apply_symm_apply y
    rw [hc, hy]
    exact e.toLinearEquiv.symm_apply_apply x
  · have := ModuleCat.subsingleton_of_isZero
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 d.pt i hi)
    refine ⟨0, 0, ?_⟩
    exact @Subsingleton.elim (((HomologicalComplex.single _ (.up ℤ) 0).obj d.pt).X i)
      (ModuleCat.subsingleton_of_isZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 d.pt i hi)) _ _

/-- 係数加群の増大列に対して、Koszul 複体の各項も単射となる。 -/
theorem koszulModule_cocone_injective {r : ℕ} (z : Fin r → R)
    (hinj : ∀ n, Function.Injective (d.ι.app n)) (n : ℕ) (i : ℤ) :
    Function.Injective (((koszulModuleFunctor z).map (d.ι.app n)).f i) :=
  koszulFunctor_map_injective z _ (single_map_injective _ (hinj n)) i

/-- 係数加群の増大列が全体を覆えば、Koszul 複体の各項も全体を覆う。 -/
theorem koszulModule_cocone_cover {r : ℕ} (z : Fin r → R)
    (hcover : ∀ x : d.pt, ∃ n y, d.ι.app n y = x) (i : ℤ)
    (x : ((koszulModuleFunctor z).obj d.pt).X i) :
    ∃ n y, (((koszulModuleFunctor z).map (d.ι.app n)).f i) y = x :=
  koszulFunctor_cocone_cover (G ⋙ HomologicalComplex.single _ (.up ℤ) 0)
    ((HomologicalComplex.single _ (.up ℤ) 0).mapCocone d) z (single_cocone_cover G d hcover) i x

end SerrePositivity
