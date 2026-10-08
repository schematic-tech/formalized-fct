# Four Color Theorem

The first complete Lean 4 proof of the Four Color Theorem for finite simple graphs. The formalization was generated autonomously by [Schematic](https://github.com/schematic-tech)'s Lean proof engine Hydra.

The main result is the theorem (established in `FourColorTheorem.Statement`):
```lean
theorem four_color_theorem
    {V : Type u} [Fintype V]
    (G : SimpleGraph V)
    IsPlanar G → G.Colorable 4 :=
  …
```

## Dependencies

- [`Schematic.Math`](https://github.com/schematic-tech/math): reusable finite graph theory, planar embeddings, hypermaps, and the Kuratowski theorem---from Schematic's formal math library.

## Related work

- [`DominatingFourColour`](https://github.com/schematic-tech/formalized-2605.10112): a significant strengthening of the Four Colour Theorem proved by António Girão, Freddie Illingworth, Bojan Mohar, Sergey Norin, Raphael Steiner, Youri Tamitegama, Jane Tan, David R. Wood, and Jung Hon Yip ([arXiv:2605.10112](https://arxiv.org/abs/2605.10112))---also formalized by Schematic Hydra.

## Build

```sh
lake update
lake build
```

Certificates use kernel reduction by default. For faster routine builds:

```sh
lake -R -K nativeDecide=true build
```

## Licenses

During formalization the proof engine Hydra accessed Georges Gonthier's Rocq repository [`rocq-community/fourcolor`](https://github.com/rocq-community/fourcolor) (copyright Microsoft Corporation and Inria and licensed under CeCILL-B).

New Lean work is Apache-2.0 licensed; see `LICENSES/Apache-2.0.txt`.
