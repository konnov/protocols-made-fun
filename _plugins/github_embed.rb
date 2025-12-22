# _plugins/github_embed.rb
#
# Download a codeblock from Github and embed it in a Jekyll post.
# Most of the credit goes to ChatGPT, which provided the initial code.

require 'open-uri'
require 'rouge'

module Jekyll
  class GitHubEmbedTag < Liquid::Tag
    def initialize(tag_name, text, tokens)
      super
      @args = text.strip.split
      @url = @args[0]
      @lang = @args[1] || 'text'
      @lines = @args[2] # e.g., "1-10"
    end

    def render(context)
      return "Missing GitHub URL" unless @url

      begin
        code = URI.open(@url).read
        if @lines
          # Support comma-separated ranges like "5-10,15-20,30-40"
          lines = code.lines
          selected_lines = []
          
          @lines.split(',').each do |range|
            if range =~ /^\d+-\d+$/
              start_line, end_line = range.split('-').map(&:to_i)
              selected_lines.concat(lines[start_line - 1..end_line - 1])
            end
          end
          
          code = selected_lines.join unless selected_lines.empty?
        end
        "```#{@lang}\n#{code}\n```"
      rescue => e
        "Error embedding GitHub code: #{e.message}"
      end
    end
  end
end

Liquid::Template.register_tag('github_embed', Jekyll::GitHubEmbedTag)