# Protocols Made Fun

Static website for <https://protocols-made-fun.com>.

The site is built with [Eleventy](https://www.11ty.dev/). It used to be a
Jekyll site, so several Jekyll-style conventions are still supported by the
Eleventy compatibility layer in `.eleventy.js`.

## Requirements

- Node.js 24 or newer
- npm

Install dependencies:

```sh
npm ci
```

## Build

Generate the site into `_site/`:

```sh
npm run build
```

Validate generated links and expected build properties:

```sh
npm run check
```

The normal build is offline. GitHub source snippets used by `{% github_embed %}`
are read from `.cache/github-embeds.json`.

## Serve Locally

Use Eleventy's development server:

```sh
npm run serve
```

If you only need to preview an already-built `_site/` directory, a plain static
server also works:

```sh
cd _site
python3 -m http.server 8080 --bind 127.0.0.1
```

Then open <http://127.0.0.1:8080/>.

## Editing Content

- Blog posts live in `_posts/`.
- Static pages live at the repository root, for example `contact.md`.
- Shared layouts live in `_layouts/`.
- Site data lives in `_data/`.
- Images and other static assets live in `assets/`, `img/`, and `specs/`.
- Main site CSS lives in `assets/css/style.css`.

Posts use YAML front matter. Existing keys such as `layout`, `title`, `date`,
`categories`, `tags`, `math`, `tlaplus`, `quint`, `lean`, and `hidden` are
preserved for compatibility.

Public post URLs use the post slug at the site root:

```text
/<slug>.html
```

For compatibility, Eleventy also emits redirect pages at the old Jekyll-style
paths:

```text
/<categories>/<year>/<month>/<day>/<slug>.html
```

Those redirect pages point to the short URL and use the short URL as their
canonical URL, so search engines should treat the short page as the primary
version.

## Syntax Highlighting

Code blocks are highlighted at build time with Highlight.js. The generated HTML
loads two CSS themes:

- `assets/css/highlight-light.css`
- `assets/css/highlight-dark.css`

They are selected with `prefers-color-scheme` by default and follow the site's
manual light/dark theme switcher when a reader chooses a theme. Do not add
client-side Highlight.js scripts to posts or layouts.

## GitHub Embeds

The custom `{% github_embed ... %}` tag renders pinned source snippets from
`.cache/github-embeds.json`.

Refresh the cache after adding or changing a GitHub embed:

```sh
npm run refresh-embeds
```

Commit the updated `.cache/github-embeds.json` together with the post change.
Normal builds should not fetch snippets from GitHub.

## Feed

The Atom feed is generated from `feed.liquid` and written to `_site/feed.xml`.
It includes post content and adds feed UTM parameters to links.

## Deployment

GitHub Pages deployment is configured in `.github/workflows/pages-deploy.yml`.
The workflow runs:

```sh
npm ci
npm run build
npm run check
```

and deploys `_site/`.
